#!/usr/bin/env python
# coding: utf-8

# # pyConditioning
# 条件づけプログラム

# バージョンアップ
# v3.5: autofocusに対応したカメラに対応させるためpicamera2を使用。

# %% モジュールの読み込み
import tkinter
from tkinter import ttk
import time
import threading
import pyaudio
import numpy as np
import logging
import random
import json
import tkinter.filedialog
import pigpio
from queue import Queue
import csv
import datetime
from decimal import Decimal, ROUND_HALF_UP
import cv2
from tkinter import messagebox
import tkinter.ttk as ttk
import math
# from MCP4922 import MCP4922
# import board
# import busio
# import adafruit_mcp4725

import RPi.GPIO as GPIO
import os
import smbus
from picamera2 import Picamera2, Preview
from picamera2.encoders import H264Encoder
from libcamera import controls, Rectangle
from picamera2.outputs.fileoutput import FileOutput
from subprocess import call #コマンド実行

import os

# %% グローバル変数
time_start=time.perf_counter() #Startボタンを押してセッションが開始したときの時刻（単位は秒）
time_end=0 #セッションの終了時間
time_trial_start=[] #各trialが始まる時間（time_startからの時間）のリスト

flag_session_start = False #セッションが開始されるとTrueになる。
flag_tone1 = True #Tone1のTrialが終わったらFalseになる
flag_tone2 = True
flag_tone3 = True
flag_solenoid1 = True
flag_solenoid2 = False
flag_opto1 = False
flag_opto2 = False
flag_opto3 = False
count_solenoid1 = 0 #solenoid1のカウンタ。solenoidをONにするたびに1つ増える。
count_solenoid2 = 0
count_tone1 = 0
count_tone2 = 0
count_tone3 = 0
count_opto1 = 0
list_tone1_time = [] #tone1の各trialが開始される時間のリスト（単位は秒数）
list_tone2_time = []
list_tone3_time = []
list_solenoid1_time = []
list_solenoid2_time = []
list_opto1_time = []
list_opto2_time = []
list_opto3_time = []
# Toneと対応するsolenoidを同時にskipしたtrialを、CSVに記録するための予定リスト
# 要素は [trial開始からの相対時刻, event名]
list_tone_solenoid_skip_events = []
# toneと対応するsolenoidを同時にskipしたtrialの、本来のtone開始予定時刻を保存するリスト
# 要素はセッション開始からの相対時刻（秒）
list_skipped_tone_times = []

# Sensor1がskipされたtone後の指定ウィンドウで検出された後、この時刻まではソレノイドを動かさない
# time.perf_counter()の絶対値で管理する
time_solenoid_block_until = 0

samples_tone1=[] #tone1のサウンドデータ
samples_tone2=[]
samples_tone3=[]

logger = logging.getLogger(__name__)



# =============================================================================
# %% 繰り返し使われる関数
# =============================================================================
def second2string(total_sec):
    """
    秒数を（HH:MM:SS）の見やすい形式の文字列に変換する
    
    Parameters
    total_sec: float
        変換したい秒数
        
    Returns
    str:
        変換された文字列
    """
    hour = total_sec // 3600
    minute = (total_sec % 3600) // 60
    second = (total_sec % 3600 % 60)
    return (str(hour).zfill(2) + ":" + str(minute).zfill(2) + ":" + str(second).zfill(2))

def get_samples(duration, freq):
    """
    指定した長さ、周波数のサイン波の音を作る
    
    Parameters
    duration: float
        音の長さ。秒単位
    freq: float
        音の周波数
        
    Returns
    numpy array:
        指定した長さ、周波数のサイン波のデータ
    """
    SAMPLE_RATE = 44100
    # SAMPLE_RATE = 10000
    if freq == 0:
        #ホワイトノイズを生成
        return np.random.normal(0,1,int(duration*SAMPLE_RATE))
    else:
        # 指定周波数のサイン波を指定秒数分生成
        return np.sin(np.arange(int(duration * SAMPLE_RATE)) * freq * np.pi * 2 / SAMPLE_RATE)

def get_shuffle_low_repeat(arr, th_seq):
    """
    0, 1で作られたnumpy行列をシャッフルする。このときに同じ数字がth_seq回連続しないになるまで、シャッフルを繰り返す
    Parameters
    arr: シャッフルする行列
    th_seq: この数−１までの連続は許容する
    Returns
    numpy array: シャッフルした行列
    """
    arr_sh = np.random.permutation(arr)
    for i in range(len(arr_sh)-th_seq):
        if np.sum(arr_sh[i:i+th_seq])==0 or np.sum(arr_sh[i:i+th_seq])==th_seq:
            return None
    return arr_sh

def get_shuffle_no_repeat(arr):
    """
    0, 1で作られたnumpy行列をシャッフルする。このときに0が連続しないになるまで、シャッフルを繰り返す
    Parameters
    arr: シャッフルする行列
    Returns
    numpy array: シャッフルした行列
    """
    arr_sh = np.random.permutation(arr)
    arr_sh_sum = arr_sh[:-1] + arr_sh[1:]
    if np.count_nonzero(arr_sh_sum==0)>0:
        return None
    else:
        return arr_sh

def get_tone_info(str_freq, str_duration):
    """
    toneの周波数、長さの文字列から情報を取得する。パルス情報含まれる場合はそれを区別して取得する
    Parameters
    str_freq: 周波数を含む文字列。パルス情報を含む場合は、音の周波数,パルスの頻度となる（4000,5など）
    str_duration: 音の長さを含む文字列。パルス情報を含む場合は、全体の長さ,パルスの長さとなる(4,0.1など)
    Returns
    freq, duration, pulse_freq, pulse_duration
    """
    if ',' in str_freq:
        freq = float(str_freq.split(',')[0])
        pulse_freq = float(str_freq.split(',')[1])
        duration = float(str_duration.split(',')[0])
        pulse_duration = float(str_duration.split(',')[1])
    else:
        freq = float(str_freq)
        pulse_freq = 0
        duration = float(str_duration)
        pulse_duration = float(str_duration)
    return freq, duration, pulse_freq, pulse_duration

def set_trial_list_regularly(type_switch, n_tone1, n_tone2, n_tone3):
    """
    trialの順番を決める関数。決め方と各trialの数から、trial順が含まれるリストを返す
    Parameters:
    type_switch, n_tone1, n_tone2, n_tone3
    """
    trial_list=[]
    if n_tone1==n_tone2 and n_tone1==n_tone3: # ３つの音を使うとき
        trial_list = ['']*int(n_tone1*3)
        if type_switch=='tone 1-2-3':
            trial_list[0::3] = ['tone1']*n_tone1
            trial_list[1::3] = ['tone2']*n_tone1
            trial_list[2::3] = ['tone3']*n_tone1
        if type_switch=='tone 2-3-1':
            trial_list[0::3] = ['tone2']*n_tone1
            trial_list[1::3] = ['tone3']*n_tone1
            trial_list[2::3] = ['tone1']*n_tone1
        if type_switch=='tone 3-2-1':
            trial_list[0::3] = ['tone3']*n_tone1
            trial_list[1::3] = ['tone2']*n_tone1
            trial_list[2::3] = ['tone1']*n_tone1
    elif n_tone3==0 and n_tone1==n_tone2:
        trial_list = ['']*int(n_tone1*2)
        if type_switch=='tone 1-2-3':
            trial_list[0::2] = ['tone1']*n_tone1
            trial_list[1::2] = ['tone2']*n_tone1
        else:
            trial_list[0::2] = ['tone2']*n_tone1
            trial_list[1::2] = ['tone1']*n_tone1
    elif n_tone2==0 and n_tone1==n_tone3:
        trial_list = ['']*int(n_tone1*2)
        if type_switch=='tone 1-2-3':
            trial_list[0::2] = ['tone1']*n_tone1
            trial_list[1::2] = ['tone3']*n_tone1
        else:
            trial_list[0::2] = ['tone3']*n_tone1
            trial_list[1::2] = ['tone1']*n_tone1
    elif n_tone1==0 and n_tone2==n_tone3:
        trial_list = ['']*int(n_tone2*2)
        if type_switch=='tone 3-2-1':
            trial_list[0::2] = ['tone3']*n_tone2
            trial_list[1::2] = ['tone2']*n_tone2
        else:
            trial_list[0::2] = ['tone2']*n_tone2
            trial_list[1::2] = ['tone3']*n_tone2
    else:
        trial_list = None
    print(trial_list)
    return trial_list

def log_output(item):
    """
    生じたイベントの名前と（セッション開始からの）時間をログとしてコンソールに出力する
    
    Parameters
    item: 型はなんでもOK
        生じたイベントの名前
    Returns なし
    """
    global time_start
    elapsed_time = time.perf_counter() - time_start
    line = "{0:3f}: {1}".format(elapsed_time, item)
    logger.info(line)

def record_timestamp():
    """
    動画のタイムスタンプを保存する

    Returns
    -------
    None.

    """
    global flag_camera, csv_file_name, list_timestamp, list_imaging_timestamp
    # camera撮影のタイムスタンプを保存する。古いカメラの場合のみ使用
    if flag_camera and not picamera2_variable.get():
        csv_timestamp = csv_file_name[:-4]+'camera_timestamp.csv'
        with open(csv_timestamp, 'a') as f:
            writer = csv.writer(f)
            for i in range(len(list_timestamp)):
                index_time = [i, list_timestamp[i]]
                writer.writerow(index_time)
    # imagingのタイムスタンプを保存する
    #imaging
    if imaging_variable.get():
        csv_imaging_timestamp = csv_file_name[:-4]+'imaging_timestamp.csv'
        with open(csv_imaging_timestamp, 'a') as f:
            writer = csv.writer(f)
            for i in range(len(list_imaging_timestamp)):
                index_time = [i, list_imaging_timestamp[i][0], list_imaging_timestamp[i][1], list_imaging_timestamp[i][2]]
#                index_time = [i, list_imaging_timestamp[i]]
                writer.writerow(index_time)

        
def draw_rectangle(event, x, y, flags, param):
    """
    カメラウィンドウでクリックすると呼ばれて、Crop範囲を設定する
    古いカメラの場合のみ使用
    """
    global camera_crop_rect, camera_rect
    if event == cv2.EVENT_LBUTTONDOWN:
        x = x*2
        y = y*2
        camera_crop_rect = [int(x-camera_rect[1]/8), int(y-camera_rect[1]/8), int(x+camera_rect[1]/8), int(y+camera_rect[1]/8)]
        if x < camera_rect[1]/8:
            camera_crop_rect[0] = 0
            camera_crop_rect[2] = int(camera_rect[1]/4)
        if x > camera_rect[0]-camera_rect[1]/8:
            camera_crop_rect[0] = int(camera_rect[0]-camera_rect[1]/4)
            camera_crop_rect[2] = camera_rect[0]
        if y < camera_rect[1]/8:
            camera_crop_rect[1] = 0
            camera_crop_rect[3] = int(camera_rect[1]/4)
        if y > camera_rect[1]/8*7:
            camera_crop_rect[1] = int(camera_rect[1]/4*3)
            camera_crop_rect[3] = camera_rect[1]
            
def lock_param_click():
    '''
    設定値をロックするチェックボックスがクリックされた時、その内容に応じて設定値をロック、あるいはロック解除する
    '''
    if lock_param_variable.get():
        state = 'disabled'
    else:
        state = '!disabled'
    list_widget = main_frm.winfo_children()
    for w in list_widget:
        w.state([state])
    # Loadボタン、experiment nameラベル、ボックス、lock checkbox, Startボタン、Cameraボタン、Estimated timeラベル、その表示ラベル、Elapsed timeラベル、その表示ラベルはロックしないようにする
    list_unlock_widget = [tone1_label, tone2_label, tone3_label, solenoid1_label, solenoid2_label, opto1_label, opto2_label, opto3_label, sensor1_label,
                          load_button, experiment_name_label, experiment_name_box, lock_check, start_button, camera_button, estimated_time_label, 
                          file_name_label, estimated_time_display, elapsed_time_label, elapsed_time_display]
    for w_unlock in list_unlock_widget:
        w_unlock.state(['!disabled'])
    
def set_pin():
    """
    画面のテキストボックスに入力されたピン番号を入出力可能にセットする
    """
    global pi
    pi.stop()
    pi = pigpio.pi()
    
    #GPIO制御の準備
    pi.set_mode(int(solenoid1_pin_box.get()), pigpio.OUTPUT)
    pi.set_mode(int(solenoid2_pin_box.get()), pigpio.OUTPUT)
    pi.set_mode(int(tone2_led_pin_box.get()), pigpio.OUTPUT)
    pi.set_mode(int(tone3_led_pin_box.get()), pigpio.OUTPUT)
    pi.set_mode(int(opto1_pin_box.get()), pigpio.OUTPUT)
    pi.set_mode(int(opto2_pin_box.get()), pigpio.OUTPUT)
    pi.set_mode(int(opto3_pin_box.get()), pigpio.OUTPUT)
    pi.set_mode(int(tone1_output_pin_box.get()), pigpio.OUTPUT)
    pi.set_mode(int(tone2_output_pin_box.get()), pigpio.OUTPUT)
    
    # ### センサーのイベント発生時に呼ばれる関数を準備
    pi.set_mode(int(sensor1_pin_box.get()), pigpio.INPUT)
    # rotary encoderの使用は停止する
    # pi.set_mode(int(rotary_encoder_pin1_box.get()), pigpio.INPUT)
    # pi.set_mode(int(rotary_encoder_pin2_box.get()), pigpio.INPUT)
    pi.set_pull_up_down(int(sensor1_pin_box.get()), pigpio.PUD_UP)
    cb = pi.callback(int(sensor1_pin_box.get()), pigpio.RISING_EDGE, event_sensor1)
    cb2 = pi.callback(int(sensor1_pin_box.get()), pigpio.FALLING_EDGE, event_sensor1)
    # cb3 = pi.callback(int(sensor2_pin_box.get()), pigpio.RISING_EDGE, event_sensor2)
    # cb4 = pi.callback(int(sensor2_pin_box.get()), pigpio.FALLING_EDGE, event_sensor2)
    if sensor2_to_tone_variable.get():
        cb3 = pi.callback(int(sensor2_pin_box.get()), pigpio.EITHER_EDGE, event_sensor2)
    if sensor3_to_tone_variable.get():
        cb8 = pi.callback(int(sensor3_pin_box.get()), pigpio.EITHER_EDGE, event_sensor3)
    # rotary encoderの使用は停止する
    # cb5 = pi.callback(int(rotary_encoder_pin1_box.get()), pigpio.RISING_EDGE, rotary_encoder_increase)
    cb6 = pi.callback(int(imaging_stamp_pin_box.get()), pigpio.RISING_EDGE, event_imaging_stamp)
    cb7 = pi.callback(int(imaging_stamp_pin_box.get()), pigpio.FALLING_EDGE, event_imaging_stamp)    
# =============================================================================
# %% マルチスレッドとして繰り返される処理
# =============================================================================
def elapsed_timer():
    """
    経過時間を表示する。マルチスレッドの１つとして実行される
    
    Parameters なし
    Returns なし
    """
    global time_start, time_end, flag_session_start, q, flag_quit, list_tone1_time, count_tone1, list_tone2_time, count_tone2, list_tone3_time, count_tone3
    while flag_session_start:
        # 経過時間を表示する
        elapsed_time = int(time.perf_counter() - time_start)
        elapsed_time_display["text"] = second2string(elapsed_time)
        # 次のtrialまでの残り時間を表示する
        time_to_next_trial = [9999,9999,9999,9999,9999]
        if len(list_tone1_time) > count_tone1:
            time_to_next_trial[0] = math.ceil(time_start + list_tone1_time[count_tone1] - time.perf_counter())
        if len(list_tone2_time) > count_tone2:
            time_to_next_trial[1] = math.ceil(time_start + list_tone2_time[count_tone2] - time.perf_counter())
        if len(list_tone3_time) > count_tone3:
            time_to_next_trial[2] = math.ceil(time_start + list_tone3_time[count_tone3] - time.perf_counter())
        if len(list_solenoid1_time) > count_solenoid1:
            time_to_next_trial[3] = math.ceil(time_start + list_solenoid1_time[count_solenoid1] - time.perf_counter())
        if len(list_solenoid2_time) > count_solenoid2:
            time_to_next_trial[4] = math.ceil(time_start + list_solenoid2_time[count_solenoid2] - time.perf_counter())

        time_to_next_trial_display["text"] = second2string(np.min(time_to_next_trial))
        # 次のtrialがtoneだったら
        if np.argmin(time_to_next_trial)<3:
            next_trial_display["text"] = '次tone' + str(np.argmin(time_to_next_trial)+1)
        else:
            next_trial_display["text"] = 'next:sol ' + str(np.argmin(time_to_next_trial)-2)
        if np.argmin(time_to_next_trial)==0:
            next_trial_display["text"] = next_trial_display["text"] + "白"
            next_trial_display["background"] = 'white'
        elif np.argmin(time_to_next_trial)==1:
            next_trial_display["text"] = next_trial_display["text"] + "青"
            next_trial_display["background"] = 'lightblue'        
        # 終了時刻になったら終了する
        if time.perf_counter() > time_end:
            q.put([time.perf_counter()-time_start, "end"])
            flag_session_start = False
            flag_quit = True
            # Cancelボタンを無効化し、Startを押せるようにする
            start_button["state"] = "active"
            cancel_button["state"] = "disable"
            elapsed_time_display["text"]="Completed"
            record_timestamp()
            #セッションのパラメーターを保存する
            experiment_info={'start_time': time_start, 'end_time': time.perf_counter()}
            saveParameter(experiment_info)
            # imaging LEDをOFFにする
            if imaging_2leds_variable.get():
                pi.write(int(imaging_led1_pin_box.get()),0)
                pi.write(int(imaging_led2_pin_box.get()),0)
            # DA変換の終了
            if focus_lens_variable.get():
                # dac.setVoltage(0, 0)
                # dac.setVoltage(1, 0)
                # dac.setVoltage(0, 0)
                # dac.setVoltage(1, 0)

                # dac.shutdown(0)
                # dac.shutdown(1)
                # GPIO.cleanup()
                dac.normalized_value = 0
            if flag_camera and not picamera2_variable.get():
                try:
                    videowriter.release()
                except NameError:
                    print('no videowriter')
        time.sleep(0.1)

# ### 音を出力する
#def tone_common_timer(item, queue, flag_tone, list_tone_time, count_tone, samples_tone, duration, pin, log_output, LED_pin):
def tone_common_timer(item, queue, flag_tone, list_tone_time, count_tone, samples_tone, duration, pin, log_output, LED_pin, LED_freq, LED_duration):

    """
    音を出力する。tone1_timerとtone2_timerの共通部分
    
    Parameters
    item: str
        "tone1" or "tone2"。CSVファイルに書き込まれるイベント名として使われる
    queue Queue.queue:
        イベントを処理するキューのクラス
    flag_tone: bool
        まだ音を出力するのであればTrue、最後のtrialになったらFalse
    list_tone_time: list (float)
        音を出力する開始時間を含むリスト
    count_tone: int
        いま、その音の出力は何回目か        
    samples_tone: numpy array
        出力する音のデータ
    duration float:
        出力する音の長さ（秒数）
    pin:
        TTL出力するピンの番号
    log_output:
        音の再生に合わせてログを出力するか
    LED_pin:
        LED点灯のために出力するピンの番号。Noneの場合は出力しない
    LED_freq:
        LED点滅の頻度
    LED_duration:
        LED点滅のパルスの時間長さ
    Returns
    count_tone: int
        いま、その音の出力は何回目か
    flag_tone: bool
        まだ音を出力するのであればTrue、最後のtrialになったらFalse
    """
    global time_start, flag_session_start, stream, SAMPLE_RATE, pi, list_tone1_volume
    if time.perf_counter()>time_start + list_tone_time[count_tone]:
        # TTL出力をON
        if type(pin)==int:
            pi.write(pin,1)
        else:
            pi.write(pin[0],1)
            pi.write(pin[1],1)
        # LED点灯
        if LED_pin is not None:
#            pi.write(LED_pin, 1)
            #LED 上の行は不要になる
            #LED LEDを明滅させるスレッドを開始する LED_pin, freq, pulse_duration, tone_duration
            th = threading.Thread(target=led_timer, args=(queue, LED_pin, LED_freq, LED_duration, duration,))
            th.start()
        
        time_sound_start = time.perf_counter()
        #音量をばらつかせるかどうか
        if tone1_volume_variable.get() and item=='tone1':
            queue.put([time_sound_start-time_start, item+"_on_"+str(list_tone1_volume[count_tone])])
            s = samples_tone * list_tone1_volume[count_tone]
            # ストリームに渡して再生
            stream.write(s.astype(np.float32).tobytes())
        elif tone1_volume_variable.get() and item=='tone3':
            queue.put([time_sound_start-time_start, item+"_on_"+str(list_tone1_volume[count_tone])])
            s = samples_tone * list_tone1_volume[count_tone]
            # ストリームに渡して再生
            stream.write(s.astype(np.float32).tobytes())
        else:
#            if LED_pin is not None:
#                queue.put([time_sound_start-time_start, "LED"+item[-1]+"_on"])
            #LED 上の行は不要になる
            if log_output:
                queue.put([time_sound_start-time_start, item+"_on"])
            # ストリームに渡して再生
            stream.write(samples_tone.astype(np.float32).tobytes())
#            stream.write(samples_tone.astype(np.float32).tostring())
        # 音の長さだけ時間が経過するのを待つ（ストリームに渡して再生すると、実際の音の再生よりも少し早く戻ってくるので、その分、待つ
        while time.perf_counter() < time_sound_start + duration:
            time.sleep(0.000001)
        # LEDを消灯
#        if LED_pin is not None:
#            pi.write(LED_pin, 0)
            #LED 上の行は不要になる
        
        # TTL出力をOFF
        if type(pin)==int:
            pi.write(pin,0)
        else:
            pi.write(pin[0],0)
            pi.write(pin[1],0)
        if log_output:
            queue.put([time.perf_counter()-time_start, item+"_off"])
        if LED_pin is not None:
            queue.put([time.perf_counter()-time_start, "LED"+item[-1]+"_off"])

        count_tone = count_tone + 1
        #音trialの最後であればこれ以上Toneは出力しない
        if count_tone == len(list_tone_time):
            flag_tone = False
    return count_tone, flag_tone
   
def tone1_timer(queue):
    """
    tone1の時間になったらtone1を出力する。マルチスレッドの１つとして実行される
    
    Parameters
    queue: Queue.queue
    
    Returns なし
    """
    global time_start, flag_session_start, flag_tone1, list_tone1_time, count_tone1, samples_tone1
#    duration = float(tone1_duration_box.get())
#    duration = float(tone1_duration_box.get().split(',')[0])
    freq, duration, pulse_freq, duration = get_tone_info(tone1_freq_box.get(), tone1_duration_box.get())
    pin = int(tone1_output_pin_box.get())
    # log_output = float(tone1_volume1_box.get())>0
    log_output = True
    while flag_session_start and flag_tone1:
#        count_tone1, flag_tone1 = tone_common_timer("tone1", queue, flag_tone1, list_tone1_time, count_tone1
#                                                    , samples_tone1, duration, pin, log_output, None)
        #LED
        count_tone1, flag_tone1 = tone_common_timer("tone1", queue, flag_tone1, list_tone1_time, count_tone1
                                                    , samples_tone1, duration, pin, log_output, None, None, None)
        time.sleep(0.000001)

def tone2_timer(queue):
    """
    tone2の時間になったらtone2を出力する。マルチスレッドの１つとして実行される
    
    Parameters
    queue: Queue.queue
    
    Returns なし
    """
    global time_start, flag_session_start, flag_tone2, list_tone2_time, count_tone2, samples_tone2
#    duration = float(tone2_duration_box.get())
    freq, duration, pulse_freq, duration = get_tone_info(tone2_freq_box.get(), tone2_duration_box.get())
    pin = int(tone2_output_pin_box.get())
    # log_output = float(tone1_volume1_box.get())>0
    log_output = True
    if tone2_led_variable.get():
        LED_pin = int(tone2_led_pin_box.get())
        LED_freq = float(tone2_led_freq_box.get())
        LED_duration = float(tone2_led_duration_box.get())
        
    else:
        LED_pin = None
        LED_freq = None
        LED_duration = None
    while (flag_session_start and flag_tone2):
#        count_tone2, flag_tone2 = tone_common_timer("tone2", queue, flag_tone2, list_tone2_time, count_tone2
#                                                    , samples_tone2, duration, pin, log_output, LED_pin)
        #LED
        count_tone2, flag_tone2 = tone_common_timer("tone2", queue, flag_tone2, list_tone2_time, count_tone2
                                                    , samples_tone2, duration, pin, log_output, LED_pin, LED_freq, LED_duration)
        time.sleep(0.000001)             

def tone3_timer(queue):
    """
    tone3の時間になったらtone3を出力する。マルチスレッドの１つとして実行される
    
    Parameters
    queue: Queue.queue
    
    Returns なし
    """
    global time_start, flag_session_start, flag_tone3, list_tone3_time, count_tone3, samples_tone3
    freq, duration, pulse_freq, duration = get_tone_info(tone3_freq_box.get(), tone3_duration_box.get())
#    duration = float(tone3_duration_box.get())
    pin = [int(tone1_output_pin_box.get()), int(tone2_output_pin_box.get())]
    # log_output = float(tone1_volume1_box.get())>0
    log_output = True
    if tone3_led_variable.get():
        LED_pin = int(tone3_led_pin_box.get())
        LED_freq = float(tone3_led_freq_box.get())
        LED_duration = float(tone3_led_duration_box.get())
    else:
        LED_pin = None
        LED_freq = None
        LED_duration = None
    while (flag_session_start and flag_tone3):
#        count_tone3, flag_tone3 = tone_common_timer("tone3", queue, flag_tone3, list_tone3_time, count_tone3
#                                                    , samples_tone3, duration, pin, log_output, LED_pin)
        #LED
        count_tone3, flag_tone3 = tone_common_timer("tone3", queue, flag_tone3, list_tone3_time, count_tone3
                                                    , samples_tone3, duration, pin, log_output, LED_pin, LED_freq, LED_duration)
        time.sleep(0.000001)             

# ### オプトの光を出力する
def opto_common_timer(item, queue, flag_opto, list_opto_time, count_opto, duration, pin):
    """
    PINをONにする。opto1_timerとopto2_timerの共通部分
    
    Parameters
    item: str
        "opto1" or "opto2"。CSVファイルに書き込まれるイベント名として使われる
    queue Queue.queue:
        イベントを処理するキューのクラス
    flag_opto: bool
        まだoptoを出力するのであればTrue、最後のtrialになったらFalse
    list_opto_time: list (float)
        optoを出力する開始時間を含むリスト
    count_opto: int
        いま、そのoptoの出力は何回目か        
    duration float:
        出力するoptoの長さ（秒数）
    pin:
        TTL出力するピンの番号
        
    Returns
    count_opto: int
        いま、そのoptoの出力は何回目か
    flag_opto: bool
        まだoptoを出力するのであればTrue、最後のtrialになったらFalse
    """
    global time_start, flag_session_start, pi
    if time.perf_counter()>time_start + list_opto_time[count_opto]:
        count_opto = count_opto + 1
        #solenoid trialの最後であればこれ以上solenoidは出力しない
        if count_opto == len(list_opto_time):
            flag_opto = False
        queue.put([time.perf_counter()-time_start, item+"_on"])
        # opto1をON
        pi.write(pin,1)
        #opto1_duration_box.get()の秒数だけ待機
        time.sleep(duration)
        # opto1をOFF
        pi.write(pin,0)
        queue.put([time.perf_counter()-time_start, item+"_off"])
    return count_opto, flag_opto

def opto1_timer(queue):
    """
    opto1の時間になったらopto1のピンをONにする。マルチスレッドの１つとして実行される
    
    Parameters
    queue: Queue.queue
    
    Returns なし
    """
    global time_start, flag_session_start, flag_opto1, list_opto1_time, count_opto1
    duration = float(opto1_duration_box.get())
    pin = int(opto1_pin_box.get())
    while flag_session_start and flag_opto1:
        count_opto1, flag_opto1 = opto_common_timer("opto1", queue, flag_opto1, list_opto1_time, count_opto1
                                                    , duration, pin)
        time.sleep(0.000001)
    
def opto2_timer(queue):
    """
    opto1の時間になったらopto1のピンをONにする。マルチスレッドの１つとして実行される
    
    Parameters
    queue: Queue.queue
    
    Returns なし
    """
    global time_start, flag_session_start, flag_opto2, list_opto2_time, count_opto2
    duration = float(opto2_duration_box.get())
    pin = int(opto2_pin_box.get())
    while flag_session_start and flag_opto2:
        count_opto2, flag_opto2 = opto_common_timer("opto2", queue, flag_opto2, list_opto2_time, count_opto2
                                                    , duration, pin)
        time.sleep(0.000001)

def opto3_timer(queue):
    """
    opto3の時間になったらopto3のピンをONにする。マルチスレッドの１つとして実行される
    
    Parameters
    queue: Queue.queue
    
    Returns なし
    """
    global time_start, flag_session_start, flag_opto3, list_opto3_time, count_opto3
    duration = float(opto3_duration_box.get())
    pin = int(opto3_pin_box.get())
    while flag_session_start and flag_opto3:
        count_opto3, flag_opto3 = opto_common_timer("opto3", queue, flag_opto3, list_opto3_time, count_opto3
                                                    , duration, pin)
        time.sleep(0.000001)

def solenoid_common_timer(item, queue, flag_solenoid, list_solenoid_time, count_solenoid, duration, pin):
    """
    ソレノイドをONにする（スクロース水を与える）。solenoid1_timerとsolenoid2_timerの共通部分

    Sensor1が「skipされたtone後x秒以内」に検出された場合、
    GUIで指定したy秒間はソレノイドをONにせずskipする。
    
    Parameters
    item: str
        "solenoid1" or "solenoid2"。CSVファイルに書き込まれるイベント名として使われる
    queue Queue.queue:
        イベントを処理するキューのクラス
    flag_solenoid: bool
        まだソレノイドをONにするのであればTrue、最後のtrialになったらFalse
    list_solenoid_time: list (float)
        ソレノイドをONにする開始時間を含むリスト
    count_solenoid: int
        いま、そのソレノイドの出力は何回目か        
    duration: float:
        ソレノイドをONにする長さ（秒数）
    pin: int
        ソレノイドと対応したRaspberry pieのピン番号
                
    Returns
    count_solenoid: int
        いま、そのソレノイドの出力は何回目か   
    flag_solenoid: bool
        まだソレノイドをONにするのであればTrue、最後のtrialになったらFalse    
    """
    global time_start, flag_session_start, pi, time_solenoid_block_until
    if time.perf_counter()>time_start + list_solenoid_time[count_solenoid]:
        now = time.perf_counter()
        count_solenoid = count_solenoid + 1
        #solenoid trialの最後であればこれ以上solenoidは出力しない
        if count_solenoid == len(list_solenoid_time):
            flag_solenoid = False

        # Sensor1による禁止期間中なら、このsolenoidイベントはONにせずskipする
        if now < time_solenoid_block_until:
            queue.put([now-time_start, item+"_blocked_by_sensor1_after_skipped_tone"])
            return count_solenoid, flag_solenoid

        queue.put([now-time_start, item+"_on"])
        # solenoid1をON
        pi.write(pin,1)
        #solenoid1_duration_box.get()の秒数だけ待機
        time.sleep(duration)
        # solenoid1をOFF
        pi.write(pin,0)
        queue.put([time.perf_counter()-time_start, item+"_off"])
    return count_solenoid, flag_solenoid

def solenoid1_timer(queue):
    """
    solenoid1の時間になったらsolenoid1をONにする。マルチスレッドの１つとして実行される
    
    Parameters
    queue: Queue.queue
    
    Returns なし
    """
    global time_start, flag_session_start, flag_solenoid1, list_solenoid1_time
    global count_solenoid1
    pin = int(solenoid1_pin_box.get())
    duration = float(solenoid1_duration_box.get())
    while flag_session_start and flag_solenoid1:
        count_solenoid1, flag_solenoid1 = solenoid_common_timer("solenoid1", queue, flag_solenoid1, list_solenoid1_time
                                                , count_solenoid1, duration, pin)
        time.sleep(0.000001)
def solenoid2_timer(queue):
    """
    solenoid2の時間になったらsolenoid2をONにする。マルチスレッドの１つとして実行される
    
    Parameters
    queue: Queue.queue
    
    Returns なし
    """
    global time_start, flag_session_start, flag_solenoid2, list_solenoid2_time
    global count_solenoid2
    pin = int(solenoid2_pin_box.get())
    duration = float(solenoid2_duration_box.get())
    while flag_session_start and flag_solenoid2:
        count_solenoid2, flag_solenoid2 = solenoid_common_timer("solenoid2", queue, flag_solenoid2, list_solenoid2_time
                                                , count_solenoid2, duration, pin)
        time.sleep(0.000001)

# 問題なければ削除する
#imaging 
#def imaging_timer(queue): 
#    """
#    イメージングカメラで撮影する。マルチスレッドの１つとして実行される
#    Parameters なし
#    Returns なし
#    """
#    global time_start, pi, list_time_imaging_trigger, flag_imaging_led1_test, flag_imaging_led2_test, next_imaging_focus
#    global dac
#    time_trigger_next = time.perf_counter()
#    list_time_imaging_trigger=[]
#    while flag_session_start:
#        if time.perf_counter() > time_trigger_next:
#            if imaging_2leds_variable.get():
#                if flag_imaging_led1_test == False:
#                    flag_imaging_led1_test = True
#                    flag_imaging_led2_test = False
#                    pi.write(int(imaging_led1_pin_box.get()),1)
#                    pi.write(int(imaging_led2_pin_box.get()),0)
#                else:
#                    flag_imaging_led1_test = False
#                    flag_imaging_led2_test = True
#                    pi.write(int(imaging_led1_pin_box.get()),0)
#                    pi.write(int(imaging_led2_pin_box.get()),1)
#            if focus_lens_variable.get():
#                list_current = focus_voltage_box.get().split(",")
#                c = int(list_current[next_imaging_focus])
#                if c>4096:
#                    c=4096
#                dac.setVoltage(0, c)
#                next_imaging_focus += 1
#                if next_imaging_focus >= len(list_current):
#                    next_imaging_focus = 0
#            pi.write(int(imaging_trigger_pin_box.get()),1)
#            list_time_imaging_trigger.append(time.perf_counter())
#            time.sleep(0.01)
#            pi.write(int(imaging_trigger_pin_box.get()),0)
#            time_trigger_next = time_trigger_next + 1.0/float(imaging_fps_box.get())
#        time.sleep(0.000001)

def feedback_timer(event, time_event):
    '''
    time_eventの時間を過ぎたらeventで指定された機能を実施する
    '''
    global samples_tone1, samples_tone2
    flag_done = False
    freq, duration, pulse_freq, duration = get_tone_info(tone1_freq_box.get(), tone1_duration_box.get())

    while flag_done == False:
        t = time.perf_counter()-time_start
        if t > time_event:
            q.put([t, event+"_on"])
            flag_done = True
            if event.startswith('tone1'):
                pin = int(tone1_output_pin_box.get())
                pi.write(pin,1) # TTL出力
                stream.write(samples_tone1.astype(np.float32).tobytes()) #音再生
                freq, duration, pulse_freq, pulse_duration = get_tone_info(tone1_freq_box.get(), tone1_duration_box.get())
                # 音の長さだけ時間が経過するのを待つ（ストリームに渡して再生すると、実際の音の再生よりも少し早く戻ってくるので、その分、待つ
                while time.perf_counter() < time_event + duration:
                    time.sleep(0.000001)
                pi.write(pin,0) # TTL出力OFF
            elif event == 'solenoid1':
                solenoid_test_common(event,solenoid1_pin_box, solenoid1_duration_box)
            elif event.startswith('tone2'):
                pin = int(tone2_output_pin_box.get())
                pi.write(pin,1) # TTL出力
                stream.write(samples_tone2.astype(np.float32).tobytes())
                freq, duration, pulse_freq, pulse_duration = get_tone_info(tone2_freq_box.get(), tone2_duration_box.get())
                # 音の長さだけ時間が経過するのを待つ（ストリームに渡して再生すると、実際の音の再生よりも少し早く戻ってくるので、その分、待つ
                while time.perf_counter() < time_event + duration:
                    time.sleep(0.000001)
                pi.write(pin,0) # TTL出力OFF
            elif event == 'solenoid2':
                solenoid_test_common(event,solenoid2_pin_box, solenoid2_duration_box)
            q.put([t, event+"_off"])
        time.sleep(0.000001)

# def record_camera_timestamp(request):
#     global time_start, list_timestamp, picam2
#     # print(picam2.capture_metadata()["SensorTimestamp"])
#     # list_timestamp.append(picam2.capture_metadata()["SensorTimestamp"])
#     list_timestamp.append(time.perf_counter()-time_start)

#mp4形式に変換&h264形式のファイル削除
def chMp4(file_name):
    # エラーが出る場合はgpacをインストールする
    # sudo apt-get install gpac
	#h264形式をmp4形式に変換
	cmdcvt = "MP4Box -add " + file_name + ".h264 " + file_name + ".mp4" #コマンド
	call([cmdcvt], shell = True) #コマンド実行

	#h264形式のファイルを削除
	cmdrm = "rm " + file_name + ".h264" #コマンド
	call([cmdrm], shell = True) #コマンド実行
        
def camera_timer(queue):
    """
    カメラで撮影する。マルチスレッドの１つとして実行される
    Parameters なし
    Returns なし
    """
    global time_start, flag_camera, list_timestamp, videowriter, video_capture, camera_rect, camera_crop_rect
    global picam2, fname_video, csv_file_name
    if picamera2_variable.get():
        # 新しいカメラを使う場合はpicamera2でないといけない
        picam2 = Picamera2()
        #HDRをオンにする
        os.system("v4l2-ctl --set-ctrl wide_dynamic_range=1 -d /dev/v4l-subdev0")
        flag_camera_crop = camera_crop_variable.get()
        fullReso = picam2.camera_properties['PixelArraySize']  # センサー解像度
        w_preview = int(fullReso[0]//5)
        h_preview = int(fullReso[1]//5)
        scalerCropWH = (fullReso[0], fullReso[1])
        #  = デジタルズーム
        zoom_ratio = camera_zoom_variable.get()
        halfReso = [ int( s // zoom_ratio ) for s in scalerCropWH ]
        leftTop = [ ( f - l ) // 2 for f, l in zip( scalerCropWH, halfReso ) ]
        picam2.start_preview(Preview.QTGL)
        encoder = H264Encoder(bitrate=10000000)
        picam2.configure(picam2.create_video_configuration(main={"format": 'XRGB8888', "size": (w_preview, h_preview)}))
        #カメラを連続オートフォーカスモードにする
        supported_controls = picam2.camera_controls
        if "AfMode" in supported_controls:
            picam2.set_controls({"AfMode": controls.AfModeEnum.Continuous})
        # デジタルズームを設定
        picam2.set_controls({"ScalerCrop": leftTop + halfReso})
        picam2.start()
        while flag_camera:
            # 事実上、アプリが終了するまで、このwhileループが継続する
            while not flag_session_start and flag_camera:
                # セッションが始まるまで、このwhileループが継続する。
                # zoom比が変更された場合の処理
                if zoom_ratio != camera_zoom_variable.get():
                    zoom_ratio = camera_zoom_variable.get()
                    if zoom_ratio < 1:
                        zoom_ratio = 1
                    halfReso = [ int( s // zoom_ratio ) for s in scalerCropWH ]
                    leftTop = [ ( f - l ) // 2 for f, l in zip( scalerCropWH, halfReso ) ]
                    picam2.set_controls({"ScalerCrop": leftTop + halfReso})
                time.sleep(0.001)
            if flag_camera:
                csv_timestamp = csv_file_name[:-4]+'camera_timestamp.csv'
                encoder.output = FileOutput(fname_video, csv_timestamp)
                # 録画スタート
                picam2.start_encoder(encoder)
                while flag_session_start:
                    time.sleep(0.001)
                # 録画終了
                picam2.stop_encoder()
                chMp4(fname_video[:-5]) #mp4形式へ変換

        #HDRをオフにする
        os.system("v4l2-ctl --set-ctrl wide_dynamic_range=0 -d /dev/v4l-subdev0")
        picam2.stop()
    else:
        # 古いカメラを使う場合
        video_capture = cv2.VideoCapture(0)
        cv2.namedWindow('camera')
        cv2.setMouseCallback('camera', draw_rectangle)

        flag_camera_crop = camera_crop_variable.get()
        if video_capture.isOpened():
            ret, frame = video_capture.read()
            camera_rect = [frame.shape[1], frame.shape[0]]
            camera_crop_rect = [int(camera_rect[0]/2-camera_rect[1]/8), int(camera_rect[1]/8*3), int(camera_rect[0]/2+camera_rect[1]/8), int(camera_rect[1]/8*5)]        
            while flag_camera:
                ret, frame = video_capture.read()
    #            frame = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
                w = frame.shape[1]
                h = frame.shape[0]
                frame_disp = np.copy(frame)
    #            frame_disp = frame
                
                if flag_camera_crop:
                    cv2.rectangle(frame_disp, (camera_crop_rect[0], camera_crop_rect[1]), (camera_crop_rect[2], camera_crop_rect[3]), color=(0,0,255), thickness=2)
    #                cv2.rectangle(frame_disp, (int(w/2-h/8),int(h/8*3)), (int(w/2+h/8),int(h/8*5)), color=(0,0,255), thickness=2)
                cv2.imshow('camera', cv2.resize(frame_disp,(int(w/2), int(h/2))))
                if flag_session_start:
                    if flag_camera_crop:
                        videowriter.write(frame[camera_crop_rect[1]:camera_crop_rect[3], camera_crop_rect[0]:camera_crop_rect[2]])
                    else:
                        videowriter.write(frame)
                    list_timestamp.append(time.perf_counter()-time_start)
    #            time.sleep(0.01)
                key = cv2.waitKey(1)
            video_capture.release()
            try:
                videowriter.release()
            except NameError:
                print('no videowriter')
            cv2.destroyAllWindows()		
        else:
            video_capture.release()
    
def led_timer(queue, pin, LED_freq, LED_duration, tone_duration):
    """
    LEDの点滅を開始する
    LED_freqの頻度で、LED_durationのパルス長さで、全体としてtone_durationの長さ、pinに電圧を出力する。そのたびにログも出力する
    """
    global time_start, pi
    time_led_end = time.perf_counter() + tone_duration
    time_led_next = time.perf_counter()
    while time.perf_counter() < time_led_end:
        if time.perf_counter() > time_led_next:
            pi.write(pin,1)
            if queue is not None:
                queue.put([time.perf_counter()-time_start, "LED_on"])
            time.sleep(LED_duration)
            pi.write(pin,0)
            if queue is not None:
                queue.put([time.perf_counter()-time_start, "LED_off"])
            time_led_next = time_led_next + 1.0/LED_freq
        time.sleep(0.000001)
        
def tone_pulse_timer(freq, duration, pulse_freq, pulse_duration, vol):
    """
    音をパルスで出力する
    """
    samples = get_samples(pulse_duration, freq) * vol
    time_tone_end = time.perf_counter() + duration
    time_tone_next = time.perf_counter()
    while time.perf_counter() < time_tone_end:
        if time.perf_counter() > time_tone_next:
            stream.write(samples.astype(np.float32).tobytes())
            time_tone_next = time_tone_next + 1.0/pulse_freq
        time.sleep(0.000001)    
    
def record_csv(q):
    """
    キューを取得してCSVファイルに書き込む。マルチスレッドの１つとして実行
    Parameters
    queue: Queue.queue

    Returns なし    
    """
    global flag_session_start, csv_file_name, flag_quit
    while flag_session_start or not flag_quit or not q.empty():
        if not q.empty():
            event = q.get()
            event[0] = float(Decimal(str(event[0])).quantize(Decimal('0.001'), rounding=ROUND_HALF_UP))
            log_output(event)
            # ここでCSVファイルに書き込み
            with open(csv_file_name, 'a') as f:
                writer = csv.writer(f)
                writer.writerow(event)
            q.task_done()
        time.sleep(0.1)

def record_walking_distance(q):
    """
    キューを取得してCSVファイルに書き込む。マルチスレッドの１つとして実行
    Parameters
    queue: Queue.queue

    Returns なし    
    """
    global flag_session_start, csv_file_name, flag_quit
    fname = csv_file_name[:-4] + '_dist.csv'
    rec_time = 0
    rec_interval = 0.1
#    while flag_session_start or not flag_quit:
#        dist = int(walking_distance_display["text"])
#        elapsed_time = (time.perf_counter() - time_start)
#        if elapsed_time > rec_time:
#            # ここでCSVファイルに書き込み
#            with open(fname, 'a') as f:
#                writer = csv.writer(f)
#                writer.writerow([round(elapsed_time,3), str(dist)])
#            rec_time = rec_time + rec_interval
#        time.sleep(0.01)

def record_temperature(q):
    """
    キューを取得してCSVファイルに書き込む。マルチスレッドの１つとして実行
    Parameters
    queue: Queue.queue

    Returns なし    
    """
    global flag_session_start, csv_file_name, flag_quit
    fname = csv_file_name[:-4] + '_temp.csv'
    rec_time = 0
    rec_interval = 0.2
    i2c = smbus.SMBus(1)
    addr=0x0a

    while flag_session_start or not flag_quit:
        elapsed_time = (time.perf_counter() - time_start)
        if elapsed_time > rec_time:
            # ここで温度を読み取る
            data = i2c.read_i2c_block_data(addr,0x4c,5)
            temp=(data[3]*256 +data[2])/10.0
            temperature_display["text"] = str(temp)
            # ここでCSVファイルに書き込み
            with open(fname, 'a') as f:
                writer = csv.writer(f)
                writer.writerow([round(elapsed_time,3), str(temp)])
            rec_time = rec_time + rec_interval
        time.sleep(0.01)

# %% イベント発生時に呼ばれる関数

def _get_float_from_entry(entry_widget, default=0.0):
    """
    GUIのEntryからfloat値を取得する。空欄や不正値の場合はdefaultを返す。
    """
    try:
        return float(entry_widget.get())
    except (ValueError, tkinter.TclError):
        return default


def _get_probability_from_entry(entry_widget, item_name):
    """
    GUIのEntryから確率値を取得する。
    確率は0以上1以下に限定し、不正値の場合はNoneを返す。
    """
    try:
        p = float(entry_widget.get())
    except (ValueError, tkinter.TclError):
        messagebox.showerror('error', f'Set numeric value for {item_name}')
        return None
    if p < 0 or p > 1:
        messagebox.showerror('error', f'Set {item_name} between 0 and 1')
        return None
    return p


def _make_probability_skip_list(n_trials, skip_probability):
    """
    trialごとに独立に乱数を引き、skipするtrialを1、通常trialを0として返す。
    skip_probability=0.2なら、各trialで20%の確率でtoneと対応solenoidを同時にskipする。
    """
    return [1 if random.random() < skip_probability else 0 for _ in range(n_trials)]


def _append_tone_time(list_tone_time, trial_start, latency, freq_box, duration_box):
    """
    通常toneまたはpulse toneの開始時刻をlist_tone_timeに追加する。
    """
    freq, duration, pulse_freq, pulse_duration = get_tone_info(freq_box.get(), duration_box.get())
    if pulse_freq == 0:
        list_tone_time.append(trial_start + float(latency.get()))
    else:
        n_tone_pulse = int(duration * pulse_freq)
        pulse_interval = 1.0 / pulse_freq
        for j in range(n_tone_pulse):
            list_tone_time.append(trial_start + float(latency.get()) + pulse_interval*j)


def trial_skip_event_timer(queue):
    """
    Tone+solenoid linked skip trialを、予定時刻にCSVへ記録する。
    実際のtone/solenoidはスケジュールに追加しないため、このタイマーはログ専用。
    """
    global time_start, flag_session_start, list_tone_solenoid_skip_events
    count_skip = 0
    while flag_session_start and count_skip < len(list_tone_solenoid_skip_events):
        event_time, event_name = list_tone_solenoid_skip_events[count_skip]
        if time.perf_counter() > time_start + event_time:
            queue.put([event_time, event_name])
            count_skip += 1
        time.sleep(0.000001)


def _update_solenoid_block_by_sensor1_after_skipped_tone(now):
    """
    Sensor1検出時に呼ばれる。
    現在時刻が「skipされたtoneの本来の開始予定時刻からx秒以内」であれば、
    GUIで指定したy秒間ソレノイドを禁止する。
    x, yはGUI上のEntryで定義する。
    """
    global time_solenoid_block_until, q, time_start, list_skipped_tone_times

    if not flag_session_start:
        return

    x = _get_float_from_entry(sensor1_after_skipped_tone_window_box, 0.0)
    y = _get_float_from_entry(sensor1_solenoid_block_duration_box, 0.0)

    # xまたはyが0以下ならブロックなし
    if x <= 0 or y <= 0:
        return

    current_elapsed = now - time_start
    if len(list_skipped_tone_times) == 0:
        return

    # skipされたtoneの本来の開始予定時刻からx秒以内にSensor1が検出された場合のみブロックする
    matched_skipped_tone_time = None
    for skipped_tone_time in sorted(list_skipped_tone_times):
        if skipped_tone_time <= current_elapsed <= skipped_tone_time + x:
            matched_skipped_tone_time = skipped_tone_time
        elif skipped_tone_time > current_elapsed:
            break

    if matched_skipped_tone_time is not None:
        time_solenoid_block_until = now + y
        q.put([round(current_elapsed, 5), "solenoid_block_start_by_sensor1_after_skipped_tone"])
        q.put([round(current_elapsed, 5), "sensor1_within_x_sec_after_skipped_tone"])
        q.put([round(matched_skipped_tone_time, 5), "matched_skipped_tone_time"])
        q.put([round(time_solenoid_block_until-time_start, 5), "solenoid_block_until"])

def event_sensor1(gpio, level, tick):
    """
    センサー１の状態が変化したときに呼ばれる
    
    Parameters
    gpio: int
    level: 
    tick: 
        
    Returns なし
    """
    global q, time_start, sensor1_label, time_solenoid1_on, list_lick_time, time_last_lick
    global time_solenoid_block_until
    if level:
        sensor1_label['foreground'] = "black" #sensor1を黒で表示する
        # 以前の「Sensor1検出で即時にsolenoid1をONにする」処理、
        # および「通常tone1後x秒より後ならsolenoidをブロックする」処理は削除。
        # 代わりに、skipされたtone後x秒以内でSensor1が検出された場合のみ、
        # GUIで指定したy秒間solenoidをブロックする。
        now = time.perf_counter()
        _update_solenoid_block_by_sensor1_after_skipped_tone(now)
    else:
        if flag_session_start:
            now = time.perf_counter()
            q.put([round(now-time_start,5), "sensor1"])
            time_last_lick = now-time_start
            list_lick_time.append(round(now-time_start,5))
        sensor1_label['foreground'] = "red" #sensor1を赤で表示する
    
#    if level:
#        if flag_session_start:
#            q.put([round(time.perf_counter()-time_start,5), "sensor1"])    
#        sensor1_label['foreground'] = "red" #sensor1を赤で表示する
#    else:
#        sensor1_label['foreground'] = "black" #sensor1を黒で表示する

def event_sensor2(gpio, level, tick):
    """
    センサー2の状態が変化したときに呼ばれる
    
    Parameters
    gpio: int
    level: 
    tick: 
        
    Returns なし
    """
    global q, time_start, sensor2_to_tone_check,time_last_feedback, list_feedback
    global list_lick_time, time_last_lick
    time_current = time.perf_counter()-time_start
    list_event = ['tone1_high', 'tone1_low', 'tone2_high', 'tone2_low']
    # センサー２がONになって、最後にフィードバックから１つ目のITI秒数経っていたら
    if flag_session_start and level==1 and time_current > time_last_feedback + float(inter_trial_interval_box1.get()): # change to high
        # さらにLick頻度で制限をかけるなら、Lick頻度が指定した数値以上であれば
        if sensor2_to_tone_param_box.get() == '': #報酬条件づけ
            if time_current > time_last_lick + 3: #最後のLickから3秒経過したら
                flag = True
            else:
                flag = False
        else: #嫌悪条件づけ
            tmp = sensor2_to_tone_param_box.get().split(',')
            th_feedback_lick_time = float(tmp[0])
            th_feedback_lick_number = float(tmp[1])
            count_lick = len(np.where(np.array(list_lick_time)>time_current-th_feedback_lick_time)[0])
            if count_lick > th_feedback_lick_number:
                flag = True
            else:
                flag = False
        if flag:        
            print(list_feedback)
            # フィードバックがtone1 or tone2のHIGHの順番であるか、tone1しかフィードバックしないなら
            if list_feedback[0] == 0 or list_feedback[0] == 2 or len(list_feedback)==0:
                event = list_event[list_feedback[0]]
                q.put([round(time_current,5), "sensor2"])    
                sensor2_to_tone_check['text'] = "SENSOR2!" #sensor2ラベルを強調表示する
                time_last_feedback = time_current
                if len(list_feedback)>0: # フィードバックの順番リストを次に進める
                    list_feedback.append(list_feedback[0])
                    list_feedback = list_feedback[1:]
                # sensor2がONになったらtoneを鳴らす設定の場合
                if sensor2_to_tone_variable.get():
                    th_tone = threading.Thread(target=feedback_timer, args=(event, time_current))
                    th_tone.start()
                    if event.startswith('tone1') and tone1_solenoid_variable.get():
                        th_solenoid = threading.Thread(target=feedback_timer, args=('solenoid1', time_current + float(solenoid1_latency_box.get())))
                        th_solenoid.start()
                    elif event.startswith('tone2') and tone2_solenoid_variable.get():
                        th_solenoid = threading.Thread(target=feedback_timer, args=('solenoid2', time_current + float(solenoid2_latency_box.get())))
                        th_solenoid.start()
    elif flag_session_start == False and level == 1:
        sensor2_to_tone_check['text'] = "SENSOR2!" #sensor2ラベルを強調表示する
        print('feedback2')
    elif level == 0: # change to low
        sensor2_to_tone_check['text'] = "Sensor2 w/ tone, pin" #sensor2ラベルを戻す
        print('feedback3')

        
def event_sensor3(gpio, level, tick):
    """
    センサー3の状態が変化したときに呼ばれる
    
    Parameters
    gpio: int
    level: 
    tick: 
        
    Returns なし
    """
    global q, time_start, sensor3_to_tone_check, time_last_feedback, list_feedback
    global time_last_lick, list_lick_time
    time_current = time.perf_counter()-time_start
    list_event = ['tone1_high', 'tone1_low', 'tone2_high', 'tone2_low']
    # センサー３がONになって、最後にフィードバックから１つ目のITI秒数経っていたら
    if flag_session_start and level==1 and time_current > time_last_feedback + float(inter_trial_interval_box1.get()): # change to high
        # フィードバックがtone1 or tone2のLOWの順番であるか、tone1しかフィードバックしないなら
        # さらにLick頻度で制限をかけるなら、Lick頻度が指定した数値以上であれば
        if sensor3_to_tone_param_box.get() == '': #報酬条件づけ
            if time_current > time_last_lick + 3: #最後のLickから3秒経過したら
                flag = True
            else:
                flag = False
        else: #嫌悪条件づけ
            tmp = sensor3_to_tone_param_box.get().split(',')
            th_feedback_lick_time = float(tmp[0])
            th_feedback_lick_number = float(tmp[1])
            count_lick = len(np.where(np.array(list_lick_time)>time_current-th_feedback_lick_time)[0])
            if count_lick > th_feedback_lick_number:
                flag = True
            else:
                flag = False
        if flag:        
            print(list_feedback)
            if list_feedback[0] == 1 or list_feedback[0] == 3 or len(list_feedback)==0:
                event = list_event[list_feedback[0]]
                time_current = time.perf_counter()-time_start
                q.put([round(time_current,5), "sensor3"])    
                sensor3_to_tone_check['text'] = "SENSOR3!" #sensor3ラベルを強調表示する
                time_last_feedback = time_current
                if len(list_feedback)>0: # フィードバックの順番リストを次に進める
                    list_feedback.append(list_feedback[0])
                    list_feedback = list_feedback[1:]

                # sensor3がONになったらtoneを鳴らす設定の場合
                if sensor3_to_tone_variable.get():
                    th_tone = threading.Thread(target=feedback_timer, args=(event, time_current))
                    th_tone.start()
                    if event.startswith('tone1') and tone1_solenoid_variable.get():
                        th_solenoid = threading.Thread(target=feedback_timer, args=('solenoid1', time_current + float(solenoid1_latency_box.get())))
                        th_solenoid.start()
                    elif event.startswith('tone2') and tone2_solenoid_variable.get():
                        th_solenoid = threading.Thread(target=feedback_timer, args=('solenoid2', time_current + float(solenoid2_latency_box.get())))
                        th_solenoid.start()
    elif flag_session_start == False and level == 1:
        sensor3_to_tone_check['text'] = "SENSOR3!" #sensor3ラベルを強調表示する
    elif level==0:
        a=1
        sensor3_to_tone_check['text'] = "Sensor3 w/ tone, pin" #sensor3ラベルを戻す

#imaging
def event_imaging_stamp(gpio, level, tick):
    """
    imaging cameraから画像取得の入力を受け取ったときに呼ばれる
    Parameters
    gpio: int
    level: 
    tick: 
        
    Returns なし
    """
    global time_start, list_imaging_timestamp, list_time_imaging_trigger
#    if level and flag_session_start:
#        if len(list_time_imaging_trigger)>0:
#            diff = time.perf_counter() - list_time_imaging_trigger.pop(0) #カメラから画像取得の入力を受け取った時間とカメラにトリガーを入れた時間の差分
#        else:
#            diff = 0
#        list_imaging_timestamp.append([time.perf_counter()-time_start, diff])
#        if len(list_time_imaging_trigger)>0 and diff > 2/float(imaging_fps_box.get()):
#            imaging_fps_label['foreground'] = "red" #fpsを赤で表示する
#        else:
#            imaging_fps_label['foreground'] = "black" #sensor1を黒で表示する
    
    # 220627変更。元に戻すなら以下を削除し、上のコメントアウトを解除する
    # カメラから画像取得のシグナルを受け取ったら、LEDを切り替えて、カメラへ画像取得のtriggerを送る
    global flag_imaging_led1_test, flag_imaging_led2_test, next_imaging_focus, flag_session_start, pi, time_trial_start, count_tone1, count_tone2, count_tone3
    global flag_within_trial
    # trial前後のみイメージングするか、その場合はイメージングする時間の範囲を決める
    if not imaging_only_trial_box.get():
        flag_whole_imaging = True #実験時間の全体をイメージングする
    else:
        flag_whole_imaging = False #Trial前後のみをイメージングする
        imaging_time_pre_post_wait = imaging_only_trial_box.get().split(",")
    # count_trial = count_tone1 + count_tone2 + count_tone3

    if level and flag_session_start:
        if flag_whole_imaging == False:
            current_time = time.perf_counter()-time_start
            rest_trial_list = np.where(np.array(time_trial_start)>current_time)[0]
            if len(rest_trial_list)>0:
                count_trial = rest_trial_list[0]
            else:
                count_trial = len(rest_trial_list)-1
            if count_trial < len(list_tone1_time) + len(list_tone2_time) + len(list_tone3_time) + int(solenoid1_only_number_box.get()) + int(solenoid2_only_number_box.get()):
                imaging_start = time_trial_start[count_trial]-float(imaging_time_pre_post_wait[0])
                imaging_end = time_trial_start[count_trial]+float(imaging_time_pre_post_wait[1])
            else:
                imaging_start = 0
                imaging_end = 0
            flag_previous_trial=False
            if count_trial>0:
                if time_trial_start[count_trial-1]-float(imaging_time_pre_post_wait[0]) < current_time < time_trial_start[count_trial-1]+float(imaging_time_pre_post_wait[1]):
                    flag_previous_trial = True
        #trialの前後のみイメージングする設定で、現在の時間がtrial前後の場合はイメージングする
        if (flag_whole_imaging == True) or (imaging_start<current_time<imaging_end) or flag_previous_trial==True:
            if focus_lens_variable.get():
                list_current = focus_voltage_box.get().split(",")
                list_imaging_timestamp.append([time.perf_counter()-time_start, 
                                        int(flag_imaging_led2_test), 
                                        (next_imaging_focus-1)%len(list_current)])

                c = float(list_current[next_imaging_focus])
                # if c>4096:
                #     c=4096
                # dac.setVoltage(0, c)
                # dac.setVoltage(0, c)
                # dac.setVoltage(0, c)
                # dac.setVoltage(0, c)
                # dac.setVoltage(0, c)
                if c>1:
                    c=1
                dac.normalized_value = c
                dac.normalized_value = c
                time.sleep(float(list_current[-1]))
                next_imaging_focus += 1
                if next_imaging_focus >= len(list_current)-1:
                    next_imaging_focus = 0
            else:
                list_imaging_timestamp.append([time.perf_counter()-time_start, 
                                int(flag_imaging_led2_test), 
                                0])
            if imaging_2leds_variable.get():
                if flag_imaging_led1_test == False:
                    flag_imaging_led1_test = True
                    flag_imaging_led2_test = False
                    pi.write(int(imaging_led1_pin_box.get()),1)
                    pi.write(int(imaging_led2_pin_box.get()),0)
                else:
                    flag_imaging_led1_test = False
                    flag_imaging_led2_test = True
                    pi.write(int(imaging_led1_pin_box.get()),0)
                    pi.write(int(imaging_led2_pin_box.get()),1)
            if flag_whole_imaging == False and imaging_2leds_variable.get() == False:
                pi.write(int(imaging_led1_pin_box.get()),1)
            pi.write(int(imaging_trigger_pin_box.get()),1)
    #        list_time_imaging_trigger.append(time.perf_counter())
            time.sleep(0.005)
            pi.write(int(imaging_trigger_pin_box.get()),0)
            flag_within_trial = True
        else:
            if 'flag_within_trial' in globals() and flag_within_trial == True:
                flag_within_trial = False
                pi.write(int(imaging_led1_pin_box.get()),0)
                pi.write(int(imaging_led2_pin_box.get()),0)
            else:
                flag_within_trial = False
            time.sleep(0.05)
            event_imaging_stamp(gpio, level, tick)

    
def solenoid_test_common(event, solenoid_pin_box, solenoid_duration_box):
    """
    ソレノイドの動作確認をする。
    
    Parameters
    event: 
    solenoid_pin_box: ttk.Entry
        ソレノイドのピン番号を入力するテキストボックス
    solenoid_duration_box: ttk.Entry
        ソレノイドをONにする時間を入力するテキストボックス
        
    Returns なし
    """
    global pi
    duration = float(solenoid_duration_box.get())
    pin = int(solenoid_pin_box.get())
    # solenoid1をON
    pi.write(pin,1)        
    #solenoid1_duration_box.get()の秒数だけ待機
    time.sleep(duration)  
     # solenoid1をOFF
    pi.write(pin,0)
    
def solenoid1_test(event):
    """
    ソレノイド１の動作確認として、指定された時間だけONにする
    
    Parameters
    event:
        
    Returns なし
    """
    th = threading.Thread(target=solenoid_test_common, args=(event,solenoid1_pin_box,solenoid1_duration_box,))
    th.start()
    
def solenoid1_open_close(event):
    """
    ソレノイド１をONにし続ける、あるいはOFFにする
    
    Parameters
    event:
        
    Returns なし
    """
    global flag_solenoid1_test, pi
    if not flag_solenoid1_test:
        event.widget['foreground'] = "red"
        flag_solenoid1_test = True
        # solenoid1をON
        pi.write(int(solenoid1_pin_box.get()),1)        
    else:
        event.widget['foreground'] = "black"
        flag_solenoid1_test = False
         # solenoid1をOFF
        pi.write(int(solenoid1_pin_box.get()),0)    

def solenoid2_test(event):
    """
    ソレノイド2の動作確認として、指定された時間だけONにする
    
    Parameters
    event:
        
    Returns なし
    """
    th = threading.Thread(target=solenoid_test_common, args=(event,solenoid2_pin_box,solenoid2_duration_box,))
    th.start()
        
def solenoid2_open_close(event):
    """
    ソレノイド2をONにし続ける、あるいはOFFにする
    
    Parameters
    event:
        
    Returns なし
    """
    global flag_solenoid2_test, pi
    if not flag_solenoid2_test:
        event.widget['foreground'] = "red"
        flag_solenoid2_test = True
        # solenoid1をON
        pi.write(int(solenoid2_pin_box.get()),1)        
    else:
        event.widget['foreground'] = "black"
        flag_solenoid2_test = False
         # solenoid1をOFF
        pi.write(int(solenoid2_pin_box.get()),0)   
        
def opto1_test(event):
    """
    ソレノイド2の動作確認として、指定された時間だけONにする
    
    Parameters
    event:
        
    Returns なし
    """
    th = threading.Thread(target=solenoid_test_common, args=(event,opto1_pin_box,opto1_duration_box,))
    th.start()
        
def opto1_open_close(event):
    """
    ソレノイド2をONにし続ける、あるいはOFFにする
    
    Parameters
    event:
        
    Returns なし
    """
    global flag_opto1_test, pi
    if not flag_opto1_test:
        event.widget['foreground'] = "red"
        flag_opto1_test = True
        # solenoid1をON
        pi.write(int(opto1_pin_box.get()),1)        
    else:
        event.widget['foreground'] = "black"
        flag_opto1_test = False
         # solenoid1をOFF
        pi.write(int(opto1_pin_box.get()),0) 
        
def opto2_test(event):
    """
    ソレノイド2の動作確認として、指定された時間だけONにする
    
    Parameters
    event:
        
    Returns なし
    """
    th = threading.Thread(target=solenoid_test_common, args=(event,opto2_pin_box,opto2_duration_box,))
    th.start()
        
def opto2_open_close(event):
    """
    ソレノイド2をONにし続ける、あるいはOFFにする
    
    Parameters
    event:
        
    Returns なし
    """
    global flag_opto2_test, pi
    if not flag_opto2_test:
        event.widget['foreground'] = "red"
        flag_opto2_test = True
        # solenoid1をON
        pi.write(int(opto2_pin_box.get()),1)        
    else:
        event.widget['foreground'] = "black"
        flag_opto2_test = False
         # solenoid1をOFF
        pi.write(int(opto2_pin_box.get()),0) 

def opto3_test(event):
    """
    ソレノイド2の動作確認として、指定された時間だけONにする
    
    Parameters
    event:
        
    Returns なし
    """
    th = threading.Thread(target=solenoid_test_common, args=(event,opto3_pin_box,opto3_duration_box,))
    th.start()
        
def opto3_open_close(event):
    """
    ソレノイド2をONにし続ける、あるいはOFFにする
    
    Parameters
    event:
        
    Returns なし
    """
    global flag_opto3_test, pi
    if not flag_opto3_test:
        event.widget['foreground'] = "red"
        flag_opto3_test = True
        # solenoid1をON
        pi.write(int(opto3_pin_box.get()),1)        
    else:
        event.widget['foreground'] = "black"
        flag_opto3_test = False
         # solenoid1をOFF
        pi.write(int(opto3_pin_box.get()),0) 

def tone1_test(event):
    """
    tone１の動作確認として、指定された時間だけONにする
    
    Parameters
    event:
        
    Returns なし
    """
   
#    samples = get_samples(float(tone1_duration_box.get()), float(tone1_freq_box.get()))
#
#    if tone1_volume_variable.get():
#        s = samples * float(tone1_volume1_box.get())
#        # ストリームに渡して再生
#        stream.write(s.astype(np.float32).tobytes())
#    else:
##        stream.write(samples.astype(np.float32).tobytes())
#        s = samples * float(tone1_volume1_box.get())
#        # ストリームに渡して再生
#        stream.write(s.astype(np.float32).tobytes())

    freq, duration, pulse_freq, pulse_duration = get_tone_info(tone1_freq_box.get(), tone1_duration_box.get())
    if pulse_freq == 0:
#        samples = get_samples(float(tone2_duration_box.get()), float(tone2_freq_box.get())) * float(tone2_volume_box.get())
        samples = get_samples(duration, freq) * float(tone1_volume1_box.get())
        stream.write(samples.astype(np.float32).tobytes())
    else:
        th2 = threading.Thread(target=tone_pulse_timer, args=(freq, duration, pulse_freq, pulse_duration, float(tone1_volume1_box.get())),)
        th2.start()
 
def tone2_test(event):
    """
    tone2の動作確認として、指定された時間だけONにする
    
    Parameters
    event:
        
    Returns なし
    """
    global pi
    if tone2_led_variable.get():
#        pi.write(int(tone2_led_pin_box.get()),1)
        #LED LEDを明滅させるスレッドを開始する LED_pin, freq, pulse_duration, tone_duration
        th = threading.Thread(target=led_timer, args=(None, int(tone2_led_pin_box.get()), 
                                                          float(tone2_led_freq_box.get()), float(tone2_led_duration_box.get()),
                                                          float(tone2_duration_box.get())),)
        th.start()
    freq, duration, pulse_freq, pulse_duration = get_tone_info(tone2_freq_box.get(), tone2_duration_box.get())
    if pulse_freq == 0:
#        samples = get_samples(float(tone2_duration_box.get()), float(tone2_freq_box.get())) * float(tone2_volume_box.get())
        samples = get_samples(duration, freq) * float(tone2_volume_box.get())
        stream.write(samples.astype(np.float32).tobytes())
    else:
        th2 = threading.Thread(target=tone_pulse_timer, args=(freq, duration, pulse_freq, pulse_duration, float(tone2_volume_box.get())),)
        th2.start()
                
#    if tone2_led_variable.get():
#        pi.write(int(tone2_led_pin_box.get()),0)
        #LED この上の行は不要になるはず
def tone3_test(event):
    """
    tone3の動作確認として、指定された時間だけONにする
    
    Parameters
    event:
        
    Returns なし
    """
    global pi
    if tone3_led_variable.get():
#        pi.write(int(tone3_led_pin_box.get()),1)
        #LED LEDを明滅させるスレッドを開始する LED_pin, freq, pulse_duration, tone_duration
        th = threading.Thread(target=led_timer, args=(None, int(tone3_led_pin_box.get()), 
                                                          float(tone3_led_freq_box.get()), float(tone3_led_duration_box.get()),
                                                          float(tone3_duration_box.get())),)
        th.start()
#    samples = get_samples(float(tone3_duration_box.get()), float(tone3_freq_box.get())) * float(tone3_volume_box.get()) 
    freq, duration, pulse_freq, pulse_duration = get_tone_info(tone3_freq_box.get(), tone3_duration_box.get())
    if pulse_freq == 0:
        samples = get_samples(duration, freq) * float(tone3_volume_box.get())
        stream.write(samples.astype(np.float32).tobytes())
    else:
        th2 = threading.Thread(target=tone_pulse_timer, args=(freq, duration, pulse_freq, pulse_duration, float(tone3_volume_box.get())),)
        th2.start()
    # if tone1_volume_variable.get():
    #     s = samples * float(tone1_volume1_box.get())
    #     # ストリームに渡して再生
    #     stream.write(s.astype(np.float32).tobytes())
    # else:
#    stream.write(samples.astype(np.float32).tobytes())
#    if tone3_led_variable.get():
#        pi.write(int(tone3_led_pin_box.get()),0)
        #LED この上の行は不要になるはず

def infrared_led_test(event):
    """
    赤外線LEDをON/OFFにする
    
    Parameters
    event:
        
    Returns なし
    """
    global flag_infrared_led_test, pi
    if not flag_infrared_led_test:
        event.widget['foreground'] = "red"
        flag_infrared_led_test = True
        # LEDをON
        pi.write(int(infrared_led_pin_box.get()),1)        
    else:
        event.widget['foreground'] = "black"
        flag_infrared_led_test = False
         # LEDをOFF
        pi.write(int(infrared_led_pin_box.get()),0) 

def imaging_led_test(event):
    """
    imaging用のLEDをON/OFFにする
    
    Parameters
    event:
        
    Returns なし
    """
    global flag_imaging_led1_test, flag_imaging_led2_test, pi
    if event.widget['text'] == 'LED1 Pin No.':
        if not flag_imaging_led1_test:
            event.widget['foreground'] = "red"
            flag_imaging_led1_test = True
            # LEDをON
            pi.write(int(imaging_led1_pin_box.get()),1)        
        else:
            event.widget['foreground'] = "black"
            flag_imaging_led1_test = False
             # LEDをOFF
            pi.write(int(imaging_led1_pin_box.get()),0) 
    elif event.widget['text'] == 'LED2 Pin No.':
        if not flag_imaging_led2_test:
            event.widget['foreground'] = "red"
            flag_imaging_led2_test = True
            # LEDをON
            pi.write(int(imaging_led2_pin_box.get()),1)        
        else:
            event.widget['foreground'] = "black"
            flag_imaging_led2_test = False
             # LEDをOFF
            pi.write(int(imaging_led2_pin_box.get()),0) 
        
def camera_start():
    """
    カメラボタンが押されたとき、カメラの撮影を開始する
    """
    global thread_camera_timer, flag_camera
    camera_crop_check["state"] = "disable"
    flag_camera = True
    thread_camera_timer = threading.Thread(target = camera_timer, args=(q,))
    thread_camera_timer.start()

# def rotary_encoder_increase(gpio, level, tick):
#     """
#     rotary encoderが進行方向に進んだときに呼ばれる
#     Parameters
#     event:
        
#     Returns なし
#     """
#     global pi, rotary_encoder_time, direction
#     try:
#         rotary_encoder_time
#     except NameError:
#         rotary_encoder_time = 0
#     diff = time.perf_counter() - rotary_encoder_time
#     dist = int(walking_distance_display["text"])
# #    if diff>0.01:
# #        if pi.read(int(rotary_encoder_pin2_box.get()))==1:
# #            direction = -1
# #        else:
# #            direction = 1
# #    rotary_encoder_time = time.perf_counter()
#     direction=1
#     dist = dist + direction
        
# #    dist=dist+1
# #    print(level, tick)
# #    if diff>0.005 and pi.read(int(rotary_encoder_pin2_box.get()))==1:
# #        dist = dist+1
# #    else:
# #        dist = dist -1
        
# #    print(gpio, pi.read(int(rotary_encoder_pin1_box.get())), pi.read(int(rotary_encoder_pin2_box.get())))
# #    if diff>0.005 and pi.read(int(rotary_encoder_pin1_box.get()))==1:
# #        rotary_encoder_time = time.perf_counter()
# #        if pi.read(int(rotary_encoder_pin2_box.get()))==1:
# #            dist = dist+1
# #        else:
# #            dist = dist-1
# #    if diff>0.005 and pi.read(int(rotary_encoder_pin1_box.get()))==0:
# #        rotary_encoder_time = time.perf_counter()
# #        if pi.read(int(rotary_encoder_pin2_box.get()))==1:
# #            dist = dist-1
# #        else:
# #            dist = dist+1
    
               
#     walking_distance_display["text"] = str(dist)
    
# %% セッションの制御       
def startSession():
    """
    セッションを開始する。Startボタンを押したときに呼ばれる
    Parameters なし
    Returns なし
    """
    global time_start, time_end, flag_session_start, list_tone1_time, list_tone2_time, list_tone3_time, flag_quit
    global list_solenoid1_time, list_solenoid2_time, time_trial_start, list_tone1_volume
    global list_opto1_time, list_opto2_time, list_opto3_time, list_lick_time
    global count_tone1, count_tone2, count_tone3, count_solenoid1, count_solenoid2, flag_tone1, flag_tone2, flag_tone3
    global count_opto1, count_opto2, count_opto3, flag_opto1, flag_opto2, flag_opto3, flag_infrared_led_test
    global flag_solenoid1, flag_solenoid2, flag_imaging_led1_test, flag_imaging_led2_test
    global samples_tone1, samples_tone2, samples_tone3, pi, csv_file_name
    global file_name_label, list_timestamp, list_imaging_timestamp
    global thread_elapsed_timer, thread_tone1_timer, thread_tone2_timer, thread_tone3_timer, thread_record_walking_distance
    global thread_solenoid1_timer, thread_solenoid2_timer, thread_record_csv, videowriter, thread_imaging_timer
    global thread_opto1_timer, thread_opto2_timer, thread_opto3_timer, thread_record_temperature
    global thread_trial_skip_event_timer, list_tone_solenoid_skip_events, list_skipped_tone_times
    global dac, next_imaging_focus, time_last_feedback, list_feedback, time_last_lick
    global picam2, fname_video
    global time_solenoid_block_until
    # 入力された値が正しそうかチェックする
    try:
        sensor1_after_skipped_tone_window_sec = float(sensor1_after_skipped_tone_window_box.get())
        sensor1_solenoid_block_sec = float(sensor1_solenoid_block_duration_box.get())
    except ValueError:
        messagebox.showerror('error', 'Set numeric values for Sensor1 skipped-tone window x and block duration y')
        return
    if sensor1_after_skipped_tone_window_sec < 0 or sensor1_solenoid_block_sec < 0:
        messagebox.showerror('error', 'Set non-negative values for Sensor1 skipped-tone window x and block duration y')
        return

    # Toneと対応するsolenoidを同時にskipする確率をGUIから取得
    tone1_solenoid_skip_probability = _get_probability_from_entry(
        tone1_solenoid_skip_probability_box, 'Tone1+Solenoid1 skip probability')
    tone2_solenoid_skip_probability = _get_probability_from_entry(
        tone2_solenoid_skip_probability_box, 'Tone2+Solenoid2 skip probability')
    if tone1_solenoid_skip_probability is None or tone2_solenoid_skip_probability is None:
        return

    #GPIO制御の準備
    set_pin()

    # Sensor1によるsolenoid禁止状態をセッション開始時にリセット
    time_solenoid_block_until = 0
#    pi.set_mode(int(solenoid1_pin_box.get()), pigpio.OUTPUT)
#    pi.set_mode(int(solenoid2_pin_box.get()), pigpio.OUTPUT)
#    pi.set_mode(int(tone2_led_pin_box.get()), pigpio.OUTPUT)
#    pi.set_mode(int(tone3_led_pin_box.get()), pigpio.OUTPUT)
#    pi.set_mode(int(opto1_pin_box.get()), pigpio.OUTPUT)
#    pi.set_mode(int(opto2_pin_box.get()), pigpio.OUTPUT)
#    pi.set_mode(int(opto3_pin_box.get()), pigpio.OUTPUT)
#    pi.set_mode(int(tone1_output_pin_box.get()), pigpio.OUTPUT)
#    pi.set_mode(int(tone2_output_pin_box.get()), pigpio.OUTPUT)

    # Focus tunable lensのためのDA変換を準備
    next_imaging_focus = 0
    if focus_lens_variable.get():
        # GPIO.setmode(GPIO.BCM)
        # dac = MCP4922()
        i2c = busio.I2C(board.SCL, board.SDA)
        dac = adafruit_mcp4725.MCP4725(i2c, address = 0x60)
        next_imaging_focus = 0

    #tone1, tone2の準備をする
    freq, duration, pulse_freq, pulse_duration = get_tone_info(tone1_freq_box.get(), tone1_duration_box.get())
    if pulse_freq == 0:
        samples_tone1 = get_samples(duration, freq)
    else:
        samples_tone1 = get_samples(pulse_duration, freq)
    freq, duration, pulse_freq, pulse_duration = get_tone_info(tone2_freq_box.get(), tone2_duration_box.get())
    if pulse_freq == 0:
        samples_tone2 = get_samples(duration, freq)
    else:
        samples_tone2 = get_samples(pulse_duration, freq)
    freq, duration, pulse_freq, pulse_duration = get_tone_info(tone3_freq_box.get(), tone3_duration_box.get())
    if pulse_freq == 0:
        samples_tone3 = get_samples(duration, freq)
    else:
        samples_tone3 = get_samples(pulse_duration, freq)
#    samples_tone1 = get_samples(float(tone1_duration_box.get()), float(tone1_freq_box.get()))
#    samples_tone2 = get_samples(float(tone2_duration_box.get()), float(tone2_freq_box.get()))
#    samples_tone3 = get_samples(float(tone3_duration_box.get()), float(tone3_freq_box.get()))
    if not tone1_volume_variable.get():
        samples_tone1 = samples_tone1 * float(tone1_volume1_box.get())
    samples_tone2 = samples_tone2 * float(tone2_volume_box.get())
    samples_tone3 = samples_tone3 * float(tone3_volume_box.get())

    #csvファイルの名前を決定
    now = datetime.datetime.now()
    csv_file_name = "{0:%Y-%m-%d}_{1}_{2:%H%M%S}.csv".format(now, experiment_name_box.get(), now)
    file_name_label["text"] = csv_file_name
    if flag_camera:
        if picamera2_variable.get():
            fname_video = csv_file_name[:-4]+'.h264'
            fps = 1000000/picam2.capture_metadata()["FrameDuration"]
            im = picam2.capture_array()
            h = int(im.shape[0]/8)
            w = int(im.shape[1]/8)
        else:
            fname_video = csv_file_name[:-4]+'.mp4'
            fps = int(video_capture.get(cv2.CAP_PROP_FPS))
            video_capture.set(cv2.CAP_PROP_FPS, fps)
            w = int(video_capture.get(cv2.CAP_PROP_FRAME_WIDTH))
            h = int(video_capture.get(cv2.CAP_PROP_FRAME_HEIGHT))
            if camera_crop_variable.get():
                w = int(h/2)
                h = int(h/2)            
            fourcc = cv2.VideoWriter_fourcc('m', 'p', '4', 'v')
            videowriter = cv2.VideoWriter(fname_video, fourcc, fps, (w, h))
    
    #各trialの開始時間を決定する（intervalをランダムに抽出して）
    nTrials = int(tone1_number_box.get()) + int(tone2_number_box.get()) + int(tone3_number_box.get()) + int(solenoid1_only_number_box.get()) + int(solenoid2_only_number_box.get())
    list_inter_trial_interval = [float(inter_trial_interval_box1.get()), float(inter_trial_interval_box2.get())
                                , float(inter_trial_interval_box3.get()), float(inter_trial_interval_box4.get())]
    time_trial_start = [list_inter_trial_interval[random.randint(0,3)]]
    for i in range(1,nTrials):
        time_next_trial = time_trial_start[i-1] + float(trial_duration_box.get())+list_inter_trial_interval[random.randint(0,3)]
        time_trial_start.append(time_next_trial)
        
    # trial順はランダムか規則正しく交互か決める
    if tone_switch_variable.get()=='Random':
        # trialのリストをシャッフルして作る
        list_trial = ["tone1"]*int(tone1_number_box.get()) + ["tone2"]*int(tone2_number_box.get()) + ["tone3"]*int(tone3_number_box.get()) \
            + ["solenoid1only"]*int(solenoid1_only_number_box.get()) + ["solenoid2only"]*int(solenoid2_only_number_box.get())
        random.shuffle(list_trial)
    else:
        # tone1-tone2-tone3の繰り返しのように規則正しく決める場合
        list_trial = set_trial_list_regularly(tone_switch_variable.get(), int(tone1_number_box.get())
                                              , int(tone2_number_box.get()), int(tone3_number_box.get()))
        if list_trial is None:
            messagebox.showerror('error', 'set trial number properly')
            return
    # 各TrialでオプトのON、OFFどちらにするかのリストを設定する
    th_seq = int(opto_max_trial_repeat_box.get())
    n_repeat = 0
    #opto1についてはランダムか、OFF-ON-OFF繰り返しか、ON-OFF-ONの繰り返しかを定める
    if opto1_switch_variable.get() != 'Random':
        list_opto1_on_off = np.array([0]*(int(tone1_number_box.get())))
        if opto1_switch_variable.get()=='OFF-ON-OFF':
            list_opto1_on_off[1::2] = 1
        if opto1_switch_variable.get()=='ON-OFF-ON':
            list_opto1_on_off[0::2] = 1
    else:
        # ランダムにON、OFFを決定する場合
        list_opto1_on_off = [1]*int(opto1_number_box.get())+[0]*(int(tone1_number_box.get())-int(opto1_number_box.get()))
        if int(opto1_number_box.get())!=0 and int(tone1_number_box.get())-int(opto1_number_box.get())!=0:
            arr_sh = None
            while arr_sh is None:
                arr_sh = get_shuffle_low_repeat(list_opto1_on_off, th_seq)
                n_repeat+=1
                if n_repeat>100000:
                    messagebox.showerror('error', 'set larger value to max_trial_repeat')
                    return
            list_opto1_on_off = arr_sh
    #opto2についてはランダムか、OFF-ON-OFF繰り返しか、ON-OFF-ONの繰り返しかを定める
    if opto2_switch_variable.get() != 'Random':
        list_opto2_on_off = np.array([0]*(int(tone2_number_box.get())))
        if opto2_switch_variable.get()=='OFF-ON-OFF':
            list_opto2_on_off[1::2] = 1
        if opto2_switch_variable.get()=='ON-OFF-ON':
            list_opto2_on_off[0::2] = 1
    else:
        # ランダムにON、OFFを決定する場合
        list_opto2_on_off = [1]*int(opto2_number_box.get())+[0]*(int(tone2_number_box.get())-int(opto2_number_box.get()))
        if int(opto2_number_box.get())!=0 and int(tone2_number_box.get())-int(opto2_number_box.get())!=0:
            arr_sh = None
            while arr_sh is None:
                arr_sh = get_shuffle_low_repeat(list_opto2_on_off, th_seq)
            list_opto2_on_off = arr_sh

    list_opto3_on_off = [1]*int(opto3_number_box.get())+[0]*(int(tone3_number_box.get())-int(opto3_number_box.get()))
    if int(opto3_number_box.get())!=0 and int(tone3_number_box.get())-int(opto3_number_box.get())!=0:
        arr_sh = None
        while arr_sh is None:
            arr_sh = get_shuffle_low_repeat(list_opto3_on_off, th_seq)
        list_opto3_on_off = arr_sh

    # 各trialでsolenoidのON、OFFのどちらにするかのリストを設定する
    n_repeat = 0
    n_trial_on = int(round(int(tone1_number_box.get())*float(solenoid1_probability_box.get())))
    n_trial_off = int(tone1_number_box.get()) - n_trial_on
    list_solenoid1_on_off = [1]*n_trial_on + [0]*n_trial_off
    if n_trial_on!=0 and n_trial_off!=0:
        arr_sh = None
        while arr_sh is None:
            arr_sh = get_shuffle_no_repeat(list_solenoid1_on_off)
            n_repeat+=1
            if n_repeat>100000:
                messagebox.showerror('error', 'set larger value to Probability')
                return
        list_solenoid1_on_off = arr_sh
    print(list_solenoid1_on_off)
    
    n_repeat = 0
    n_trial_on = int(round(int(tone2_number_box.get())*float(solenoid2_probability_box.get())))
    n_trial_off = int(tone2_number_box.get()) - n_trial_on
    list_solenoid2_on_off = [1]*n_trial_on + [0]*n_trial_off
    if n_trial_on!=0 and n_trial_off!=0:
        arr_sh = None
        while arr_sh is None:
            arr_sh = get_shuffle_no_repeat(list_solenoid2_on_off)
            n_repeat+=1
            if n_repeat>100000:
                messagebox.showerror('error', 'set larger value to Probability')
                return
        list_solenoid2_on_off = arr_sh
    print(list_solenoid2_on_off)

    # 各trialでtoneと対応するsolenoidを同時にskipするかどうかを設定する
    # 1: toneと対応solenoidを両方skip, 0: 通常通り
    # ここは各trialで独立に乱数を引くため、セッション全体のskip数は厳密固定ではない。
    list_tone1_solenoid_skip = _make_probability_skip_list(
        int(tone1_number_box.get()), tone1_solenoid_skip_probability)
    list_tone2_solenoid_skip = _make_probability_skip_list(
        int(tone2_number_box.get()), tone2_solenoid_skip_probability)
    print('list_tone1_solenoid_skip', list_tone1_solenoid_skip)
    print('list_tone2_solenoid_skip', list_tone2_solenoid_skip)
    
    #Tone1, Tone2, solenoid1, solenoid2のそれぞれn回目の開始時間を決める
    list_tone1_time=[]
    list_tone2_time=[]
    list_tone3_time=[]
    list_solenoid1_time=[]
    list_solenoid2_time=[]
    list_opto1_time=[]
    list_opto2_time=[]
    list_opto3_time=[]
    list_tone_solenoid_skip_events=[]
    list_skipped_tone_times=[]
    list_timestamp = []
    list_imaging_timestamp = []
    count_opto1=0
    count_opto2=0
    count_opto3=0
    count_solenoid1=0
    count_solenoid2=0
    for i in range(nTrials):
        if list_trial[i] == "tone1":
            skip_tone_solenoid = (list_tone1_solenoid_skip[count_solenoid1] == 1)

            if skip_tone_solenoid:
                # tone1と対応するsolenoid1を同じtrialでskipする
                # opto1は既存設定を維持するため、従来通り下で判定する
                skipped_tone_time = time_trial_start[i] + float(tone1_latency_box.get())
                list_tone_solenoid_skip_events.append([
                    skipped_tone_time,
                    "tone1_solenoid1_skipped_by_probability"
                ])
                list_skipped_tone_times.append(skipped_tone_time)
            else:
                _append_tone_time(list_tone1_time, time_trial_start[i], tone1_latency_box,
                                  tone1_freq_box, tone1_duration_box)
                if list_solenoid1_on_off[count_solenoid1] == 1 and tone1_solenoid_variable.get()==True:
                    list_solenoid1_time.append(time_trial_start[i]+float(solenoid1_latency_box.get()))

            if list_opto1_on_off[count_opto1] == 1:
                list_opto1_time.append(time_trial_start[i]+float(opto1_latency_box.get()))
            count_solenoid1+=1
            count_opto1+=1    
        elif list_trial[i] == 'tone2':
            skip_tone_solenoid = (list_tone2_solenoid_skip[count_solenoid2] == 1)

            if skip_tone_solenoid:
                # tone2と対応するsolenoid2を同じtrialでskipする
                # opto2は既存設定を維持するため、従来通り下で判定する
                skipped_tone_time = time_trial_start[i] + float(tone2_latency_box.get())
                list_tone_solenoid_skip_events.append([
                    skipped_tone_time,
                    "tone2_solenoid2_skipped_by_probability"
                ])
                list_skipped_tone_times.append(skipped_tone_time)
            else:
                _append_tone_time(list_tone2_time, time_trial_start[i], tone2_latency_box,
                                  tone2_freq_box, tone2_duration_box)
#            list_tone2_time.append(time_trial_start[i]+float(tone2_latency_box.get()))
                if list_solenoid2_on_off[count_solenoid2] == 1 and tone2_solenoid_variable.get()==True: #220715に変更した。
#            if list_solenoid2_on_off[count_solenoid2] == 1:
                    # list_solenoid2_time.append(time_trial_start[i]+float(solenoid2_latency_box.get()))
                    solenoid_pulse_interval = 1.0 / float(solenoid2_pulse_freq_box.get())
                    for j in range(int(solenoid2_pulse_number_box.get())):
                        list_solenoid2_time.append(time_trial_start[i] + float(solenoid2_latency_box.get()) + solenoid_pulse_interval * j)

            if list_opto2_on_off[count_opto2] == 1:
                list_opto2_time.append(time_trial_start[i]+float(opto2_latency_box.get()))
            count_solenoid2+=1
            count_opto2+=1    
        elif list_trial[i] == 'tone3':
            freq, duration, pulse_freq, pulse_duration = get_tone_info(tone3_freq_box.get(), tone3_duration_box.get())
            if pulse_freq == 0:
                list_tone3_time.append(time_trial_start[i]+float(tone3_latency_box.get()))
            else:
                n_tone_pulse = int(duration * pulse_freq)
                pulse_interval = 1.0 / pulse_freq
                for j in range(n_tone_pulse):
                    list_tone3_time.append(time_trial_start[i]+float(tone3_latency_box.get()) + pulse_interval*j)
#            list_tone3_time.append(time_trial_start[i]+float(tone3_latency_box.get()))
            if tone3_solenoid_variable.get() == True and tone2_solenoid_variable.get() == False:
                list_solenoid2_time.append(time_trial_start[i]+float(solenoid2_latency_box.get()))
            if list_opto3_on_off[count_opto3] == 1:
                list_opto3_time.append(time_trial_start[i]+float(opto3_latency_box.get()))
            count_opto3+=1    
        elif list_trial[i] == 'solenoid1only':
            list_solenoid1_time.append(time_trial_start[i])#+float(solenoid1_latency_box.get()))
            # count_solenoid1+=1
        elif list_trial[i] == 'solenoid2only':
            list_solenoid2_time.append(time_trial_start[i])#+float(solenoid2_latency_box.get()))
            # count_solenoid2+=1
    
    # solenoid2を独立して動作させる場合(context fear)
    if solenoid2_independent_variable.get():
         list_latency = solenoid2_session_latency_box.get().split(",")
         for latency in list_latency:
             list_solenoid2_time.append(float(latency))
        
    # skip eventのログ順を時刻順にそろえる
    list_tone_solenoid_skip_events = sorted(list_tone_solenoid_skip_events, key=lambda x: x[0])
    list_skipped_tone_times = sorted(list_skipped_tone_times)

    #tone1の音量を可変にするならリストを作る
    if tone1_volume_variable.get():
        n_trial_each_vol = int(int(tone1_number_box.get()+tone3_number_box.get())/6)
        list_tone1_volume = np.array([float(tone1_volume1_box.get())]*n_trial_each_vol + \
                            [float(tone1_volume2_box.get())]*n_trial_each_vol + \
                            [float(tone1_volume3_box.get())]*n_trial_each_vol + \
                            [float(tone1_volume4_box.get())]*n_trial_each_vol + \
                            [float(tone1_volume5_box.get())]*n_trial_each_vol + \
                            [float(tone1_volume6_box.get())]*n_trial_each_vol
                            )
#        rng = np.random.default_rng()
        list_tone1_volume = np.random.permutation(list_tone1_volume)
    # 実際にスケジュールされたイベントがある場合のみ、各タイマースレッドを起動する
    # skip確率が1でtoneが全て消える場合でも、空リスト参照によるエラーを防ぐ。
    flag_tone1 = (len(list_tone1_time) > 0)
    flag_tone2 = (len(list_tone2_time) > 0)
    flag_tone3 = (len(list_tone3_time) > 0)
    flag_solenoid1 = (len(list_solenoid1_time) > 0)
    flag_solenoid2 = (len(list_solenoid2_time) > 0)
    flag_opto1 = (len(list_opto1_time) > 0)
    flag_opto2 = (len(list_opto2_time) > 0)
    flag_opto3 = (len(list_opto3_time) > 0)
        
    #tone1, tone2, solenoid1, solenoid2のカウンターを0にする
    count_tone1=0
    count_tone2=0
    count_tone3=0
    count_solenoid1=0
    count_solenoid2=0
    count_opto1 = 0
    count_opto2 = 0
    count_opto3 = 0

    #最後にフィードバックを行った時間を初期化しておく
    time_last_feedback = 0
    #フィードバックを行う順番を決める

    if sensor2_to_tone_variable and sensor3_to_tone_variable:
        # tone1とtone2の両方を使う場合
        option_feedback_order = [[0,2,1,3,1,2,3,0,1,2,0,3],
                                [1,0,2,3,2,0,3,1,0,3,1,2],
                                [2,0,3,1,3,0,1,2,3,1,2,0],
                                [3,1,2,0,1,2,0,3,2,0,3,1]]
        list_feedback = option_feedback_order[random.randint(0,3)]
    elif (sensor2_to_tone_variable and not sensor3_to_tone_variable) or feedback_only_tone1_variable.get():
        # tone1だけ使う場合
        option_feedback_order = [[0,1,0,1,1,0,1,0,0,1],
                                [1,0,1,0,1,0,1,0,0,1],
                                [0,1,1,0,0,1,1,0,1,0],
                                [1,0,0,1,1,0,1,0,1,0]]
        list_feedback = option_feedback_order[random.randint(0,3)]
    else:
        list_feedback = []
    #タイマーをセットする
    flag_session_start = True
    #session開始時刻を取得する
    time_start = time.perf_counter()

    thread_elapsed_timer = threading.Thread(target = elapsed_timer)
    thread_elapsed_timer.start()
    if flag_tone1:
        thread_tone1_timer = threading.Thread(target = tone1_timer, args=(q,))
        thread_tone1_timer.start()
    else:
        thread_tone1_timer=None
    if flag_tone2:
        thread_tone2_timer = threading.Thread(target = tone2_timer, args=(q,))
        thread_tone2_timer.start()
    else:
        thread_tone2_timer = None
    if flag_tone3:
        thread_tone3_timer = threading.Thread(target = tone3_timer, args=(q,))
        thread_tone3_timer.start()
    else:
        thread_tone3_timer = None
    if flag_solenoid1:    
        thread_solenoid1_timer = threading.Thread(target = solenoid1_timer, args=(q,))
        thread_solenoid1_timer.start()
    else:
        thread_solenoid1_timer=None
    if flag_solenoid2:
        thread_solenoid2_timer = threading.Thread(target = solenoid2_timer, args=(q,))
        thread_solenoid2_timer.start()
    else:
        thread_solenoid2_timer=None
    if flag_opto1:    
        thread_opto1_timer = threading.Thread(target = opto1_timer, args=(q,))
        thread_opto1_timer.start()
    else:
        thread_opto1_timer=None
    if flag_opto2:    
        thread_opto2_timer = threading.Thread(target = opto2_timer, args=(q,))
        thread_opto2_timer.start()
    else:
        thread_opto2_timer=None
    if flag_opto3:    
        thread_opto3_timer = threading.Thread(target = opto3_timer, args=(q,))
        thread_opto3_timer.start()
    else:
        thread_opto3_timer=None
    
    thread_record_csv = threading.Thread(target = record_csv, args=(q,))
    thread_record_csv.start()
    if len(list_tone_solenoid_skip_events) > 0:
        thread_trial_skip_event_timer = threading.Thread(target = trial_skip_event_timer, args=(q,))
        thread_trial_skip_event_timer.start()
    else:
        thread_trial_skip_event_timer = None
    # thread_record_temperature = threading.Thread(target = record_temperature, args=(q,))
    # thread_record_temperature.start()
    # thread_record_walking_distance = threading.Thread(target = record_walking_distance, args=(q,))
    # thread_record_walking_distance.start()
    
    #imaging
    flag_imaging_led1_test = False
    flag_imaging_led2_test = False

    if imaging_variable.get():
#       thread_imaging_timer = threading.Thread(target = imaging_timer, args=(q,))
#       thread_imaging_timer.start()
       #220627変更。イメージングは、カメラから画像取得シグナルが来たらすぐにカメラに画像取得トリガーを送る形式にする。この場合はthreadではなく、ここで1回、カメラにトリガーを送る。
       # もとに戻すときは上のコメントアウトを解除して、以下を削除する
        if imaging_2leds_variable.get():
            flag_imaging_led1_test = True
            flag_imaging_led2_test = False
            pi.write(int(imaging_led1_pin_box.get()),1)
            pi.write(int(imaging_led2_pin_box.get()),0)
        if focus_lens_variable.get():
            list_current = focus_voltage_box.get().split(",")
            c = float(list_current[next_imaging_focus])
            # if c>4096:
            #     c=4096
            # dac.setVoltage(0, c)
            # dac.setVoltage(0, c)
            if c>1:
                c=1
            dac.normalized_value = c
            dac.normalized_value = c
            next_imaging_focus += 1
            if next_imaging_focus >= len(list_current):
                next_imaging_focus = 0
        pi.write(int(imaging_trigger_pin_box.get()),1)
#        list_time_imaging_trigger.append(time.perf_counter())
        time.sleep(0.01)
        pi.write(int(imaging_trigger_pin_box.get()),0)
       
    list_lick_time = []
    
    # 所要時間を計算して終了時間を設定する
    length_session = time_trial_start[nTrials-1]+float(trial_duration_box.get())+list_inter_trial_interval[random.randint(0,3)]
    estimated_time_display["text"] = second2string(int(length_session))
    time_end = time_start + length_session
    time_last_lick = 0
    #歩行距離を0にする
    # walking_distance_display["text"] = str(0)

    #Startボタンを無効化し、Cancelを押せるようにする
    start_button["state"] = "disable"
    cancel_button["state"] = "active"
    flag_quit = False
    
    
def cancelSession():
    """
    セッションを終了する。Cancelボタンが押されたとき、すべてのTrialを終えたときに呼ばれる
    Parameters　なし
    Returns なし
    """    
    global flag_session_start, q, flag_quit, flag_camera, csv_timestamp, list_timestamp, videowriter
    global thread_elapsed_timer, thread_tone1_timer, thread_tone2_timer, thread_tone3_timer
    global thread_solenoid1_timer, thread_solenoid2_timer, thread_record_csv
    global thread_opto1_timer, thread_opto2_timer, thread_opto3_timer
    global dac
    q.put([time.perf_counter()-time_start, "end"])

    flag_session_start = False
    
    # camera撮影のタイムスタンプを保存する
    if not picamera2_variable.get():
        record_timestamp()
    
    #セッションのパラメーターを保存する
    dt_now = datetime.datetime.now()
    dt_start = dt_now - datetime.timedelta(seconds = time.perf_counter() - time_start)
    experiment_info={'start_time': dt_start.strftime('%Y/%m/%d %H:%M:%S'), 'end_time': dt_now.strftime('%Y/%m/%d %H:%M:%S')}
    saveParameter(experiment_info)
    
    # imaging LEDをOFFにする
    if imaging_2leds_variable.get():
        pi.write(int(imaging_led1_pin_box.get()),0)
        pi.write(int(imaging_led2_pin_box.get()),0)
        
    #Cancelボタンを無効化し、Startを押せるようにする
    start_button["state"] = "active"
    cancel_button["state"] = "disable"
    # 古いバージョンのPythonでは以下のis_aliveをisAliveにする
    if type(thread_elapsed_timer) is threading.Thread and thread_elapsed_timer.is_alive():
        thread_elapsed_timer.join()
    if type(thread_tone1_timer) is threading.Thread and thread_tone1_timer.is_alive():
        thread_tone1_timer.join()
    if type(thread_tone2_timer) is threading.Thread:
        if thread_tone2_timer.is_alive():
            thread_tone2_timer.join()
    if type(thread_tone3_timer) is threading.Thread:
        if thread_tone3_timer.is_alive():
            thread_tone3_timer.join()
    if type(thread_solenoid1_timer) is threading.Thread and thread_solenoid1_timer.is_alive():
        thread_solenoid1_timer.join()
    if type(thread_solenoid2_timer) is threading.Thread and thread_solenoid2_timer.is_alive():
        thread_solenoid2_timer.join()
    if type(thread_opto1_timer) is threading.Thread and thread_opto1_timer.is_alive():
        thread_opto1_timer.join()
    if type(thread_opto2_timer) is threading.Thread and thread_opto2_timer.is_alive():
        thread_opto2_timer.join()
    if type(thread_opto3_timer) is threading.Thread and thread_opto3_timer.is_alive():
        thread_opto3_timer.join()
    if type(thread_trial_skip_event_timer) is threading.Thread and thread_trial_skip_event_timer.is_alive():
        thread_trial_skip_event_timer.join()
    flag_quit = True
    if type(thread_record_csv) is threading.Thread and thread_record_csv.is_alive():
        thread_record_csv.join()
    if flag_camera and not picamera2_variable.get():
        try:
            videowriter.release()
        except NameError:
            print('no videowriter')

    # DA変換の終了
    if focus_lens_variable.get():
        # dac.setVoltage(0, 0)
        # dac.setVoltage(1, 0)
        # dac.setVoltage(0, 0)
        # dac.setVoltage(1, 0)
        # dac.shutdown(0)
        # dac.shutdown(1)
        # GPIO.cleanup()
        dac.normalized_value = 0

# ### Saveボタンが押されたときに呼ばれる
def saveParameter(experiment_info=None):
    """
    Saveボタンが押されたときやセッションの終了時に呼ばれて、設定値を指定したファイルに保存する
    Parameters:
        experiment_info: セッションの終了時に呼ばれたときは、ここにセッション開始時刻、終了時刻が含まれている
    Returns なし
    """
    global csv_file_name
    log_output("save")
    # 辞書オブジェクト(dictionary)を生成
    data = dict()
    if experiment_info is not None:
        data['experiment_info'] = experiment_info
    data['pyConditioning'] = os.path.basename(__file__)
    data['experiment_name'] = experiment_name_box.get()
    data['tone1'] = {
      'frequency': tone1_freq_box.get(), 'duration': tone1_duration_box.get()
        , 'latency': tone1_latency_box.get(), 'number_of_trials': tone1_number_box.get()
        , 'with_solenoid':tone1_solenoid_variable.get(), 'pin': tone1_output_pin_box.get()
        , 'vol1': tone1_volume1_box.get(), 'vol2': tone1_volume2_box.get(), 'vol3': tone1_volume3_box.get()
        , 'vol4': tone1_volume4_box.get(), 'vol5': tone1_volume5_box.get(), 'vol6': tone1_volume6_box.get()
    }
    data['tone2'] = {
      'frequency': tone2_freq_box.get(), 'duration': tone2_duration_box.get()
        , 'latency': tone2_latency_box.get(), 'number_of_trials': tone2_number_box.get()
        , 'with_solenoid':tone2_solenoid_variable.get(), 'pin': tone2_output_pin_box.get()
        , 'vol': tone2_volume_box.get(), 'led': tone2_led_variable.get()
        , 'led_pin': tone2_led_pin_box.get(), 'led_freq': tone2_led_freq_box.get(), 'led_duration': tone2_led_duration_box.get()
    }
    data['tone3'] = {
      'frequency': tone3_freq_box.get(), 'duration': tone3_duration_box.get()
        , 'latency': tone3_latency_box.get(), 'number_of_trials': tone3_number_box.get()
        , 'vol': tone3_volume_box.get(), 'with_solenoid':tone3_solenoid_variable.get()
        , 'led': tone3_led_variable.get(), 'led_pin': tone3_led_pin_box.get()
        , 'led_freq': tone3_led_freq_box.get(), 'led_duration': tone3_led_duration_box.get()
    }
    data['solenoid1'] = {
      'duration': solenoid1_duration_box.get(), 'latency': solenoid1_latency_box.get()
        , 'pin': solenoid1_pin_box.get(), 'probability': solenoid1_probability_box.get()
        , 'number_of_sol1': solenoid1_only_number_box.get()
    }
    data['solenoid2'] = {
      'duration': solenoid2_duration_box.get(), 'latency': solenoid2_latency_box.get()
        , 'pin': solenoid2_pin_box.get(), 'probability': solenoid2_probability_box.get()
        , 'pulse_freq': solenoid2_pulse_freq_box.get(), 'pulse_number': solenoid2_pulse_number_box.get()        
        , 'number_of_sol2': solenoid2_only_number_box.get()
        , 'independent': solenoid2_independent_variable.get()
        , 'session_latency': solenoid2_session_latency_box.get()
    }
    data['tone_solenoid_skip'] = {
        'tone1_solenoid1_probability': tone1_solenoid_skip_probability_box.get(),
        'tone2_solenoid2_probability': tone2_solenoid_skip_probability_box.get()
    }
    data['opto1'] = {
      'duration': opto1_duration_box.get(), 'latency': opto1_latency_box.get()
        , 'pin': opto1_pin_box.get(), 'number_of_trials': opto1_number_box.get()
        , 'max_repeat': opto_max_trial_repeat_box.get(), 'switch': opto1_switch_variable.get()
    }
    data['opto2'] = {
      'duration': opto2_duration_box.get(), 'latency': opto2_latency_box.get()
        , 'pin': opto2_pin_box.get(), 'number_of_trials': opto2_number_box.get()
        , 'switch': opto2_switch_variable.get()
    }
    data['opto3'] = {
      'duration': opto3_duration_box.get(), 'latency': opto3_latency_box.get()
        , 'pin': opto3_pin_box.get(), 'number_of_trials': opto3_number_box.get()
    }
    data['sensor1'] = {
        'pin': sensor1_pin_box.get()
        # 旧仕様の即時solenoidは削除したため、互換性維持用にFalseで保存する
        , 'with_solenoid': False
        , 'after_skipped_tone_window_sec': sensor1_after_skipped_tone_window_box.get()
        , 'block_duration_sec': sensor1_solenoid_block_duration_box.get()
    }
    data['sensor2'] = {
        'pin': sensor2_pin_box.get()
        , 'with_tone': sensor2_to_tone_variable.get()
        , 'param': sensor2_to_tone_param_box.get()
    }
    data['sensor3'] = {
        'pin': sensor3_pin_box.get()
        , 'with_tone': sensor3_to_tone_variable.get()
        , 'param': sensor3_to_tone_param_box.get()
    }
    data['trial'] = {
        'duration': trial_duration_box.get(), 'inter_trial_interval1': inter_trial_interval_box1.get(),
        'inter_trial_interval2': inter_trial_interval_box2.get(),'inter_trial_interval3': inter_trial_interval_box3.get(),
        'inter_trial_interval4': inter_trial_interval_box4.get(), 
        'camera_crop': camera_crop_variable.get(),
        'picam2': picamera2_variable.get(),
        'camera_zoom': camera_zoom_variable.get(),
        'lock_param': lock_param_variable.get()
    }
    data['imaging'] = {
            'check': imaging_variable.get(), 'trigger_pin': imaging_trigger_pin_box.get(), 'stamp_pin': imaging_stamp_pin_box.get(), 
            'imaging_with_2leds': imaging_2leds_variable.get(), 'led1_pin': imaging_led1_pin_box.get(), 'led2_pin': imaging_led2_pin_box.get(),
            'focus_tunable_lens': focus_lens_variable.get(), 'focus_voltage': focus_voltage_box.get(), 'only_trials': imaging_only_trial_box.get()
            }
    data['rotary_encoder'] = {
        'pin1': "0", 'pin2': "0"
    }
    #init_dir = os.path.abspath(os.path.dirname())
    if experiment_info is None:
        file_name = tkinter.filedialog.asksaveasfilename(filetypes=[("JSON", ".json")], defaultextension='.json', title='Save as')
    else:
        file_name = csv_file_name[:-4]+'_parameters.json'
    log_output(file_name)
    if len(file_name)>0:
        with open(file_name, mode='wt', encoding='utf-8') as file:
            json.dump(data, file, ensure_ascii=False, indent=2)


# ### Loadボタンが押されたときに呼ばれる
def loadParameter():
    """
    Loadボタンが押されたときに呼ばれて、指定したファイルから設定値をロードする
    Parameters　なし
    Returns なし
    """
    file_name = tkinter.filedialog.askopenfilename(filetypes=[("JSON", ".json")], defaultextension='json', title='Open')
    log_output(file_name)
    # lockのチェックを解除して、全ての設定値のロックを解除する
    lock_param_variable.set(False)
    lock_param_click()
    
    with open(file_name, mode='rt', encoding='utf-8') as file:
        data = json.load(file)
        #check version
        ver_pyCond=0
        if 'pyConditioning' in data.keys():
            try:
                ver_pyCond = data['pyConditioning'][16:]
                ver_pyCond = float(ver_pyCond[:-3])
            except (ValueError, TypeError):
                # ファイル名にv3.5のような数値バージョンが含まれない派生版では、
                # 新しい形式として扱う。
                ver_pyCond = 999.0
        print(ver_pyCond)
        experiment_name_box.delete(0,"end")
        experiment_name_box.insert(0, data['experiment_name'])
        tone1_freq_box.delete(0,"end")
        tone1_freq_box.insert(0, data['tone1']['frequency'])
        tone1_duration_box.delete(0,"end")
        tone1_duration_box.insert(0, data['tone1']['duration'])
        tone1_latency_box.delete(0,"end")
        tone1_latency_box.insert(0, data['tone1']['latency'])
        tone1_number_box.delete(0,"end")
        tone1_number_box.insert(0, data['tone1']['number_of_trials'])
        tone1_solenoid_variable.set(data['tone1']['with_solenoid'])
        tone1_output_pin_box.delete(0,"end")
        tone1_output_pin_box.insert(0, data['tone1']['pin'])
        tone1_volume1_box.delete(0,"end")
        tone1_volume1_box.insert(0, data['tone1']['vol1'])
        tone1_volume2_box.delete(0,"end")
        tone1_volume2_box.insert(0, data['tone1']['vol2'])
        tone1_volume3_box.delete(0,"end")
        tone1_volume3_box.insert(0, data['tone1']['vol3'])
        tone1_volume4_box.delete(0,"end")
        tone1_volume4_box.insert(0, data['tone1']['vol4'])
        tone1_volume5_box.delete(0,"end")
        tone1_volume5_box.insert(0, data['tone1']['vol5'])
        tone1_volume6_box.delete(0,"end")
        tone1_volume6_box.insert(0, data['tone1']['vol6'])
        
        tone2_freq_box.delete(0,"end")
        tone2_freq_box.insert(0, data['tone2']['frequency'])
        tone2_duration_box.delete(0,"end")
        tone2_duration_box.insert(0, data['tone2']['duration'])
        tone2_latency_box.delete(0,"end")
        tone2_latency_box.insert(0, data['tone2']['latency'])
        tone2_number_box.delete(0,"end")
        tone2_number_box.insert(0, data['tone2']['number_of_trials'])
        tone2_solenoid_variable.set(data['tone2']['with_solenoid'])
        tone2_output_pin_box.delete(0,"end")
        tone2_output_pin_box.insert(0, data['tone2']['pin'])
        tone2_volume_box.delete(0,"end")
        tone2_volume_box.insert(0, data['tone2']['vol'])
        tone2_led_variable.set(data['tone2']['led'])
        tone2_led_pin_box.delete(0,"end")
        tone2_led_pin_box.insert(0, data['tone2']['led_pin'])
        tone2_led_freq_box.delete(0,"end")
        tone2_led_freq_box.insert(0, data['tone2']['led_freq'])
        tone2_led_duration_box.delete(0,"end")
        tone2_led_duration_box.insert(0, data['tone2']['led_duration'])
        
        tone3_freq_box.delete(0,"end")
        tone3_freq_box.insert(0, data['tone3']['frequency'])
        tone3_duration_box.delete(0,"end")
        tone3_duration_box.insert(0, data['tone3']['duration'])
        tone3_latency_box.delete(0,"end")
        tone3_latency_box.insert(0, data['tone3']['latency'])
        tone3_number_box.delete(0,"end")
        tone3_number_box.insert(0, data['tone3']['number_of_trials'])
        tone3_solenoid_variable.set(data['tone3']['with_solenoid'])
        tone3_volume_box.delete(0,"end")
        tone3_volume_box.insert(0, data['tone3']['vol'])
        tone3_led_variable.set(data['tone3']['led'])
        tone3_led_pin_box.delete(0,"end")
        tone3_led_pin_box.insert(0, data['tone3']['led_pin'])
        tone3_led_freq_box.delete(0,"end")
        tone3_led_freq_box.insert(0, data['tone3']['led_freq'])
        tone3_led_duration_box.delete(0,"end")
        tone3_led_duration_box.insert(0, data['tone3']['led_duration'])

        solenoid1_duration_box.delete(0,"end")
        solenoid1_duration_box.insert(0, data['solenoid1']['duration'])
        solenoid1_latency_box.delete(0,"end")
        solenoid1_latency_box.insert(0, data['solenoid1']['latency'])
        solenoid1_pin_box.delete(0,"end")
        solenoid1_pin_box.insert(0, data['solenoid1']['pin'])
        solenoid1_probability_box.delete(0,"end")
        solenoid1_probability_box.insert(0, data['solenoid1']['probability'])
        if ver_pyCond>=2.2:
            solenoid1_only_number_box.delete(0,"end")
            solenoid1_only_number_box.insert(0, data['solenoid1']['number_of_sol1'])

        solenoid2_duration_box.delete(0,"end")
        solenoid2_duration_box.insert(0, data['solenoid2']['duration'])
        solenoid2_latency_box.delete(0,"end")
        solenoid2_latency_box.insert(0, data['solenoid2']['latency'])
        solenoid2_pin_box.delete(0,"end")
        solenoid2_pin_box.insert(0, data['solenoid2']['pin'])
        solenoid2_probability_box.delete(0,"end")
        solenoid2_probability_box.insert(0, data['solenoid2']['probability'])
        if ver_pyCond>=1.8:
            solenoid2_pulse_freq_box.delete(0,"end")
            solenoid2_pulse_freq_box.insert(0, data['solenoid2']['pulse_freq'])
            solenoid2_pulse_number_box.delete(0,"end")
            solenoid2_pulse_number_box.insert(0, data['solenoid2']['pulse_number'])
        if ver_pyCond>=2.2:
            solenoid2_only_number_box.delete(0,"end")
            solenoid2_only_number_box.insert(0, data['solenoid2']['number_of_sol2'])
        if ver_pyCond>=3.1:
            solenoid2_independent_variable.set(data['solenoid2']['independent'])
            solenoid2_session_latency_box.delete(0,"end")
            solenoid2_session_latency_box.insert(0,data['solenoid2']['session_latency'])

        # 旧パラメータファイルには存在しないため、なければ0として扱う
        tone_solenoid_skip_data = data.get('tone_solenoid_skip', {})
        tone1_solenoid_skip_probability_box.delete(0,"end")
        tone1_solenoid_skip_probability_box.insert(0, tone_solenoid_skip_data.get('tone1_solenoid1_probability', '0'))
        tone2_solenoid_skip_probability_box.delete(0,"end")
        tone2_solenoid_skip_probability_box.insert(0, tone_solenoid_skip_data.get('tone2_solenoid2_probability', '0'))

        opto1_duration_box.delete(0,"end")
        opto1_duration_box.insert(0, data['opto1']['duration'])
        opto1_latency_box.delete(0,"end")
        opto1_latency_box.insert(0, data['opto1']['latency'])
        opto1_pin_box.delete(0,"end")
        opto1_pin_box.insert(0, data['opto1']['pin'])
        opto1_number_box.delete(0,"end")
        opto1_number_box.insert(0, data['opto1']['number_of_trials'])
        if ver_pyCond>=1.9:
            opto1_switch_variable.set(data['opto1']['switch'])

        opto2_duration_box.delete(0,"end")
        opto2_duration_box.insert(0, data['opto2']['duration'])
        opto2_latency_box.delete(0,"end")
        opto2_latency_box.insert(0, data['opto2']['latency'])
        opto2_pin_box.delete(0,"end")
        opto2_pin_box.insert(0, data['opto2']['pin'])
        opto2_number_box.delete(0,"end")
        opto2_number_box.insert(0, data['opto2']['number_of_trials'])
        if ver_pyCond>=1.9:
            opto2_switch_variable.set(data['opto2']['switch'])

        opto3_duration_box.delete(0,"end")
        opto3_duration_box.insert(0, data['opto3']['duration'])
        opto3_latency_box.delete(0,"end")
        opto3_latency_box.insert(0, data['opto3']['latency'])
        opto3_pin_box.delete(0,"end")
        opto3_pin_box.insert(0, data['opto3']['pin'])
        opto3_number_box.delete(0,"end")
        opto3_number_box.insert(0, data['opto3']['number_of_trials'])

        sensor1_pin_box.delete(0,"end")
        sensor1_pin_box.insert(0, data['sensor1']['pin'])
        # 旧仕様の即時solenoidは使わないため、Load時もFalseにする
        sensor1_to_solenoid1_variable.set(False)
        sensor1_after_skipped_tone_window_box.delete(0,"end")
        sensor1_after_skipped_tone_window_box.insert(0, data.get('sensor1', {}).get('after_skipped_tone_window_sec', '0'))
        sensor1_solenoid_block_duration_box.delete(0,"end")
        sensor1_solenoid_block_duration_box.insert(0, data.get('sensor1', {}).get('block_duration_sec', '0'))
        if ver_pyCond>=2.7:
            sensor2_pin_box.delete(0,"end")
            sensor2_pin_box.insert(0, data['sensor2']['pin'])
            sensor3_pin_box.delete(0,"end")
            sensor3_pin_box.insert(0, data['sensor3']['pin'])
            sensor2_to_tone_variable.set(data['sensor2']['with_tone'])
            sensor3_to_tone_variable.set(data['sensor3']['with_tone'])
        trial_duration_box.delete(0,"end")
        trial_duration_box.insert(0, data['trial']['duration'])
        inter_trial_interval_box1.delete(0,"end")
        inter_trial_interval_box1.insert(0, data['trial']['inter_trial_interval1'])
        inter_trial_interval_box2.delete(0,"end")
        inter_trial_interval_box2.insert(0, data['trial']['inter_trial_interval2'])
        inter_trial_interval_box3.delete(0,"end")
        inter_trial_interval_box3.insert(0, data['trial']['inter_trial_interval3'])
        inter_trial_interval_box4.delete(0,"end")
        inter_trial_interval_box4.insert(0, data['trial']['inter_trial_interval4'])
        camera_crop_variable.set(data['trial']['camera_crop'])
        if ver_pyCond>=3.5:
            picamera2_variable.set(data['trial']['picam2']) 
            camera_zoom_variable.set(data['trial']['camera_zoom'])        
        if ver_pyCond>=3.0:
            lock_param_variable.set(data['trial']['lock_param'])        
        imaging_variable.set(data['imaging']['check'])
        imaging_trigger_pin_box.delete(0,"end")
        imaging_trigger_pin_box.insert(0, data['imaging']['trigger_pin'])
        imaging_stamp_pin_box.delete(0,"end")
        imaging_stamp_pin_box.insert(0, data['imaging']['stamp_pin'])
        imaging_2leds_variable.set(data['imaging']['imaging_with_2leds'])
        imaging_led1_pin_box.delete(0,"end")
        imaging_led1_pin_box.insert(0, data['imaging']['led1_pin'])
        imaging_led2_pin_box.delete(0,"end")
        imaging_led2_pin_box.insert(0, data['imaging']['led2_pin'])
        focus_lens_variable.set(data['imaging']['focus_tunable_lens'])
        focus_voltage_box.delete(0,"end")
        focus_voltage_box.insert(0, data['imaging']['focus_voltage'])
        if ver_pyCond>=2.3:
            imaging_only_trial_box.delete(0,"end")
            imaging_only_trial_box.insert(0, data['imaging']['only_trials'])
        # rotary_encoder_pin1_box.delete(0,"end")
        # rotary_encoder_pin1_box.insert(0, data['rotary_encoder']['pin1'])
        # rotary_encoder_pin2_box.delete(0,"end")
        # rotary_encoder_pin2_box.insert(0, data['rotary_encoder']['pin2'])
    lock_param_click()
    set_pin()
    
# ### 終了ボタンが押されたときに呼ばれる関数
def quit_app():
    """
    終了ボタンが押されたときに呼ばれて、終了のための処理を行う
    Parameters　なし
    Returns なし
    
    """
    global thread_elapsed_timer, thread_tone1_timer, thread_tone2_timer, thread_tone3_timer, flag_session_start
    global thread_solenoid1_timer, thread_solenoid2_timer, thread_record_csv, main_win
    global thread_opto1_timer, thread_opto2_timer, thread_opto3_timer
    global flag_camera, thread_camera_timer
    global p, stream, pi
    if flag_session_start:
        cancelSession()
    if flag_camera==True:
        flag_camera=False
        thread_camera_timer.join()
        
    stream.close()
    p.terminate()
    pi.stop()
    
    # thread1終了後にアプリ終了
    main_win.destroy()

# %% メインウインドウとメインフレームの作成
# メインウィンドウ
main_win = tkinter.Tk()
main_win.title("pyConditioning")
main_win.geometry("1050x780")

# メインフレーム
main_frm = ttk.Frame(main_win)
main_frm.grid(column=0, row=0, sticky=tkinter.NSEW, padx=5, pady=10)
main_frm.columnconfigure(0, weight=0)
main_frm.columnconfigure(1, weight=6)
main_frm.columnconfigure(2, weight=0)
main_frm.columnconfigure(3, weight=7)
main_frm.columnconfigure(4, weight=3)
main_frm.columnconfigure(5, weight=7)
main_frm.columnconfigure(6, weight=5)
main_frm.columnconfigure(7, weight=10)

# %% ウィジェットの作成
# ウィジェット作成（Experiment name）
experiment_name_label = ttk.Label(main_frm, text="Experiment name", font=("Arial", 12,"bold"))
experiment_name_box = ttk.Entry(main_frm)
file_name_label = ttk.Label(main_frm, text="")

#tone1について
tone1_label = ttk.Label(main_frm, text="Tone 1", font=("Arial", 12,"bold"))
tone1_label.bind("<1>", func=tone1_test)
tone1_freq_label = ttk.Label(main_frm, text="Freq(Hz) (,pulse freq(Hz))")
tone1_freq_box = ttk.Entry(main_frm)
tone1_freq_box.insert(0,'10000')

tone1_duration_label = ttk.Label(main_frm, text="Duration (s) (,pulse length(s))")
tone1_duration_box = ttk.Entry(main_frm)
tone1_duration_box.insert(0,'0.5')

tone1_latency_label = ttk.Label(main_frm, text="Latency from trial onset (s)")
tone1_latency_box = ttk.Entry(main_frm)
tone1_latency_box.insert(0,'0')

tone1_number_label = ttk.Label(main_frm, text="Number of trials")
tone1_number_box = ttk.Entry(main_frm)
tone1_number_box.insert(0,'100')

tone1_solenoid_variable = tkinter.BooleanVar() 
tone1_solenoid_variable.set(True)
tone1_solenoid_check = ttk.Checkbutton(main_frm, text="solenoid", var=tone1_solenoid_variable)

tone1_output_pin_label = ttk.Label(main_frm, text="Tone1 Output Pin No.")
tone1_output_pin_box = ttk.Entry(main_frm)
tone1_output_pin_box.insert(0, '18')

tone1_volume_variable = tkinter.BooleanVar() 
tone1_volume_variable.set(False)
tone1_volume_variable_check = ttk.Checkbutton(main_frm, text="Vol variable", var=tone1_volume_variable)
tone1_volume1_box = ttk.Entry(main_frm)
tone1_volume1_box.insert(0, '0.1')
tone1_volume2_box = ttk.Entry(main_frm)
tone1_volume2_box.insert(0, '0.2')
tone1_volume3_box = ttk.Entry(main_frm)
tone1_volume3_box.insert(0, '0.4')
tone1_volume4_box = ttk.Entry(main_frm)
tone1_volume4_box.insert(0, '0.6')
tone1_volume5_box = ttk.Entry(main_frm)
tone1_volume5_box.insert(0, '0.8')
tone1_volume6_box = ttk.Entry(main_frm)
tone1_volume6_box.insert(0, '1')

#tone2について
tone2_label = ttk.Label(main_frm, text="Tone 2", font=("Arial", 12,"bold"))
tone2_label.bind("<1>", func=tone2_test)
tone2_freq_label = ttk.Label(main_frm, text="Freq(Hz) (,pulse freq(Hz))")
tone2_freq_box = ttk.Entry(main_frm)
tone2_freq_box.insert(0,'10000')

tone2_duration_label = ttk.Label(main_frm, text="Duration (s) (,pulse length(s))")
tone2_duration_box = ttk.Entry(main_frm)
tone2_duration_box.insert(0,'2')

tone2_volume_label = ttk.Label(main_frm, text="Volume (0-1)")
tone2_volume_box = ttk.Entry(main_frm)
tone2_volume_box.insert(0,'0.1')

tone2_latency_label = ttk.Label(main_frm, text="Latency from trial onset (s)")
tone2_latency_box = ttk.Entry(main_frm)
tone2_latency_box.insert(0, '0')

tone2_number_label = ttk.Label(main_frm, text="Number of trials")
tone2_number_box = ttk.Entry(main_frm)
tone2_number_box.insert(0, '0')

tone2_solenoid_variable = tkinter.BooleanVar() 
tone2_solenoid_variable.set(False)
tone2_solenoid_check = ttk.Checkbutton(main_frm, text="solenoid2", var=tone2_solenoid_variable)

tone2_output_pin_label = ttk.Label(main_frm, text="Tone2 Output Pin No.")
tone2_output_pin_box = ttk.Entry(main_frm)
tone2_output_pin_box.insert(0, '19')

tone2_led_variable = tkinter.BooleanVar() 
tone2_led_variable.set(False)
tone2_led_check = ttk.Checkbutton(main_frm, text="LED", var=tone2_led_variable)

tone2_led_pin_label = ttk.Label(main_frm, text="LED Pin No.")
tone2_led_pin_box = ttk.Entry(main_frm)
tone2_led_pin_box.insert(0, '12')

tone2_led_freq_label = ttk.Label(main_frm, text="LED freq (Hz)")
tone2_led_freq_box = ttk.Entry(main_frm)
tone2_led_freq_box.insert(0, '5')

tone2_led_duration_label = ttk.Label(main_frm, text="LED duration (s)")
tone2_led_duration_box = ttk.Entry(main_frm)
tone2_led_duration_box.insert(0, '0.1')

#tone3について
tone3_label = ttk.Label(main_frm, text="Tone 3", font=("Arial", 12,"bold"))
tone3_label.bind("<1>", func=tone3_test)
tone3_freq_label = ttk.Label(main_frm, text="Freq(Hz) (,pulse freq(Hz))")
tone3_freq_box = ttk.Entry(main_frm)
tone3_freq_box.insert(0,'0')

tone3_duration_label = ttk.Label(main_frm, text="Duration (s) (,pulse length(s))")
tone3_duration_box = ttk.Entry(main_frm)
tone3_duration_box.insert(0,'2')

tone3_volume_label = ttk.Label(main_frm, text="Volume (0-1)")
tone3_volume_box = ttk.Entry(main_frm)
tone3_volume_box.insert(0,'0.1')

tone3_latency_label = ttk.Label(main_frm, text="Latency from trial onset (s)")
tone3_latency_box = ttk.Entry(main_frm)
tone3_latency_box.insert(0, '0')

tone3_number_label = ttk.Label(main_frm, text="Number of trials")
tone3_number_box = ttk.Entry(main_frm)
tone3_number_box.insert(0, '0')

tone3_solenoid_variable = tkinter.BooleanVar() 
tone3_solenoid_variable.set(False)
tone3_solenoid_check = ttk.Checkbutton(main_frm, text="solenoid2", var=tone3_solenoid_variable)

tone3_led_variable = tkinter.BooleanVar() 
tone3_led_variable.set(False)
tone3_led_check = ttk.Checkbutton(main_frm, text="LED", var=tone3_led_variable)

tone3_led_pin_label = ttk.Label(main_frm, text="LED Pin No.")
tone3_led_pin_box = ttk.Entry(main_frm)
tone3_led_pin_box.insert(0, '12')

tone3_led_freq_label = ttk.Label(main_frm, text="LED freq (Hz)")
tone3_led_freq_box = ttk.Entry(main_frm)
tone3_led_freq_box.insert(0, '5')

tone3_led_duration_label = ttk.Label(main_frm, text="LED duration (s)")
tone3_led_duration_box = ttk.Entry(main_frm)
tone3_led_duration_box.insert(0, '0.1')

tone_switch_label = ttk.Label(main_frm, text="Tone switch")
tone_option_switch = ['Random', 'tone 1-2-3', 'tone 2-3-1', 'tone 3-2-1']
tone_switch_variable = tkinter.StringVar()
tone_switch_combo = ttk.Combobox(main_frm, textvariable=tone_switch_variable, values=tone_option_switch,width=10)
tone_switch_combo.set(tone_option_switch[0])

#solenoid1について
solenoid1_label = ttk.Label(main_frm, text="Solenoid 1", font=("Arial", 12,"bold"))
solenoid1_label.bind("<1>", func=solenoid1_test)
solenoid1_label.bind("<3>", func=solenoid1_open_close)

solenoid1_probability_label = ttk.Label(main_frm, text="Probability (0-1)")
solenoid1_probability_box = ttk.Entry(main_frm)
solenoid1_probability_box.insert(1,'1')

# tone1と対応するsolenoid1を同じtrialでskipする確率
tone1_solenoid_skip_probability_label = ttk.Label(main_frm, text="T1+S1 skip prob (0-1)")
tone1_solenoid_skip_probability_box = ttk.Entry(main_frm)
tone1_solenoid_skip_probability_box.insert(0,'0')

solenoid1_duration_label = ttk.Label(main_frm, text="Duration (s)")
solenoid1_duration_box = ttk.Entry(main_frm)
solenoid1_duration_box.insert(0,'0.045')

solenoid1_latency_label = ttk.Label(main_frm, text="Latency from trial onset (s)")
solenoid1_latency_box = ttk.Entry(main_frm)
solenoid1_latency_box.insert(0, '0.3')

solenoid1_pin_label = ttk.Label(main_frm, text="Pin No.")
solenoid1_pin_box = ttk.Entry(main_frm)
solenoid1_pin_box.insert(0, '6')

solenoid1_only_number_label = ttk.Label(main_frm, text="Sol1 only#")
solenoid1_only_number_box = ttk.Entry(main_frm)
solenoid1_only_number_box.insert(0, '0')

#solenoid2について
solenoid2_label = ttk.Label(main_frm, text="Solenoid 2", font=("Arial", 12,"bold"))
solenoid2_label.bind("<1>", func=solenoid2_test)
solenoid2_label.bind("<3>", func=solenoid2_open_close)

solenoid2_probability_label = ttk.Label(main_frm, text="Probability (0-1)")
solenoid2_probability_box = ttk.Entry(main_frm)
solenoid2_probability_box.insert(1,'1')

# tone2と対応するsolenoid2を同じtrialでskipする確率
tone2_solenoid_skip_probability_label = ttk.Label(main_frm, text="T2+S2 skip prob (0-1)")
tone2_solenoid_skip_probability_box = ttk.Entry(main_frm)
tone2_solenoid_skip_probability_box.insert(0,'0')

solenoid2_duration_label = ttk.Label(main_frm, text="Duration (s)")
solenoid2_duration_box = ttk.Entry(main_frm)
solenoid2_duration_box.insert(0,'0.050')

solenoid2_latency_label = ttk.Label(main_frm, text="Latency from trial onset (s)")
solenoid2_latency_box = ttk.Entry(main_frm)
solenoid2_latency_box.insert(0, '3')

solenoid2_pin_label = ttk.Label(main_frm, text="Pin No.")
solenoid2_pin_box = ttk.Entry(main_frm)
solenoid2_pin_box.insert(0, '5')

solenoid2_pulse_freq_label = ttk.Label(main_frm, text="Pulse freq (Hz)")
solenoid2_pulse_freq_box = ttk.Entry(main_frm)
solenoid2_pulse_freq_box.insert(0, '1')
solenoid2_pulse_number_label = ttk.Label(main_frm, text="Pulse No.")
solenoid2_pulse_number_box = ttk.Entry(main_frm)
solenoid2_pulse_number_box.insert(0, '1')

solenoid2_only_number_label = ttk.Label(main_frm, text="Sol2 only#")
solenoid2_only_number_box = ttk.Entry(main_frm)
solenoid2_only_number_box.insert(0, '0')

#opto1について
opto1_label = ttk.Label(main_frm, text="Opto 1", font=("Arial", 12,"bold"))
opto1_label.bind("<1>", func=opto1_test)
opto1_label.bind("<3>", func=opto1_open_close)

opto1_duration_label = ttk.Label(main_frm, text="Duration (s)")
opto1_duration_box = ttk.Entry(main_frm)
opto1_duration_box.insert(0,'0.050')

opto1_latency_label = ttk.Label(main_frm, text="Latency from trial onset (s)")
opto1_latency_box = ttk.Entry(main_frm)
opto1_latency_box.insert(0, '2')

opto1_number_label = ttk.Label(main_frm, text="#ON trials")
opto1_number_box = ttk.Entry(main_frm)
opto1_number_box.insert(0, '0')

opto1_pin_label = ttk.Label(main_frm, text="Pin No.")
opto1_pin_box = ttk.Entry(main_frm)
opto1_pin_box.insert(0, '20')

opto_max_trial_repeat_label = ttk.Label(main_frm, text="Max trial repeat")
opto_max_trial_repeat_box = ttk.Entry(main_frm)
opto_max_trial_repeat_box.insert(0, '4')

opto1_switch_label = ttk.Label(main_frm, text="ON-OFF switch")
option_switch = ['Random', 'OFF-ON-OFF', 'ON-OFF-ON']
opto1_switch_variable = tkinter.StringVar()
opto1_switch_combo = ttk.Combobox(main_frm, textvariable=opto1_switch_variable, values=option_switch,width=10)
opto1_switch_combo.set(option_switch[0])

#opto2について
opto2_label = ttk.Label(main_frm, text="Opto 2", font=("Arial", 12,"bold"))
opto2_label.bind("<1>", func=opto2_test)
opto2_label.bind("<3>", func=opto2_open_close)

opto2_duration_label = ttk.Label(main_frm, text="Duration (s)")
opto2_duration_box = ttk.Entry(main_frm)
opto2_duration_box.insert(0,'0.050')

opto2_latency_label = ttk.Label(main_frm, text="Latency from trial onset (s)")
opto2_latency_box = ttk.Entry(main_frm)
opto2_latency_box.insert(0, '2')

opto2_number_label = ttk.Label(main_frm, text="#ON trials")
opto2_number_box = ttk.Entry(main_frm)
opto2_number_box.insert(0, '0')

opto2_pin_label = ttk.Label(main_frm, text="Pin No.")
opto2_pin_box = ttk.Entry(main_frm)
opto2_pin_box.insert(0, '20')

opto2_switch_label = ttk.Label(main_frm, text="ON-OFF switch")
option_switch = ['Random', 'OFF-ON-OFF', 'ON-OFF-ON']
opto2_switch_variable = tkinter.StringVar()
opto2_switch_combo = ttk.Combobox(main_frm, textvariable=opto2_switch_variable, values=option_switch,width=10)
opto2_switch_combo.set(option_switch[0])

#opto3について
opto3_label = ttk.Label(main_frm, text="Opto 3", font=("Arial", 12,"bold"))
opto3_label.bind("<1>", func=opto3_test)
opto3_label.bind("<3>", func=opto3_open_close)

opto3_duration_label = ttk.Label(main_frm, text="Duration (s)")
opto3_duration_box = ttk.Entry(main_frm)
opto3_duration_box.insert(0,'0.050')

opto3_latency_label = ttk.Label(main_frm, text="Latency from trial onset (s)")
opto3_latency_box = ttk.Entry(main_frm)
opto3_latency_box.insert(0, '2')

opto3_number_label = ttk.Label(main_frm, text="#ON trials")
opto3_number_box = ttk.Entry(main_frm)
opto3_number_box.insert(0, '0')

opto3_pin_label = ttk.Label(main_frm, text="Pin No.")
opto3_pin_box = ttk.Entry(main_frm)
opto3_pin_box.insert(0, '16')

#sensor
sensor1_label = ttk.Label(main_frm, text="Sensor 1", font=("Arial", 12,"bold"))
sensor1_pin_label = ttk.Label(main_frm, text="Pin No.")
sensor1_pin_box = ttk.Entry(main_frm)
sensor1_pin_box.insert(0, '26')
sensor1_after_skipped_tone_window_label = ttk.Label(main_frm, text="Block if Sensor1 within x s after skipped tone")
sensor1_after_skipped_tone_window_box = ttk.Entry(main_frm)
sensor1_after_skipped_tone_window_box.insert(0, '0')
sensor1_solenoid_block_duration_label = ttk.Label(main_frm, text="Solenoid block y (s)")
sensor1_solenoid_block_duration_box = ttk.Entry(main_frm)
sensor1_solenoid_block_duration_box.insert(0, '0')
# sensor2_label = ttk.Label(main_frm, text="Sensor 2", font=("Arial", 12,"bold"))
# sensor2_pin_label = ttk.Label(main_frm, text="Pin No.")
sensor2_pin_box = ttk.Entry(main_frm)
sensor2_pin_box.insert(0, '17')
sensor3_pin_box = ttk.Entry(main_frm)
sensor3_pin_box.insert(0, '18')

# senser to tone
sensor2_to_tone_variable = tkinter.BooleanVar() 
sensor2_to_tone_variable.set(False)
sensor2_to_tone_check = ttk.Checkbutton(main_frm, text="Sensor2 w/ tone, Pin", var=sensor2_to_tone_variable)
sensor2_to_tone_param_label = ttk.Label(main_frm, text="sec for lick, num")
sensor2_to_tone_param_box = ttk.Entry(main_frm)
sensor2_to_tone_param_box.insert(0, '')

sensor3_to_tone_variable = tkinter.BooleanVar() 
sensor3_to_tone_variable.set(False)
sensor3_to_tone_check = ttk.Checkbutton(main_frm, text="Sensor3 w/ tone, Pin", var=sensor3_to_tone_variable)
sensor3_to_tone_param_label = ttk.Label(main_frm, text="sec for lick, num")
sensor3_to_tone_param_box = ttk.Entry(main_frm)
sensor3_to_tone_param_box.insert(0, '')

feedback_only_tone1_variable = tkinter.BooleanVar() 
feedback_only_tone1_variable.set(False)
feedback_only_tone1_check = ttk.Checkbutton(main_frm, text="fb t1", var=feedback_only_tone1_variable)

# trial-independent solenoid2
solenoid2_independent_variable = tkinter.BooleanVar() 
solenoid2_independent_variable.set(False)
solenoid2_independent_check = ttk.Checkbutton(main_frm, text="Sol2 independent", var=solenoid2_independent_variable)
solenoid2_session_latency_box = ttk.Entry(main_frm)


# #rotary encoder
# rotary_encoder_label = ttk.Label(main_frm, text="Rotary encoder", font=("Arial", 12,"bold"))
# rotary_encoder_pin_label = ttk.Label(main_frm, text="Pin No.")
# rotary_encoder_pin1_box = ttk.Entry(main_frm)
# rotary_encoder_pin1_box.insert(0, '23')
# rotary_encoder_pin2_box = ttk.Entry(main_frm)
# rotary_encoder_pin2_box.insert(0, '24')


#Trial
trial_duration_label = ttk.Label(main_frm, text="Trial duration (s)")
trial_duration_box = ttk.Entry(main_frm)
trial_duration_box.insert(0, '0')
inter_trial_interval_label = ttk.Label(main_frm, text="Inter trial interval (s)")
inter_trial_interval_box1 = ttk.Entry(main_frm)
inter_trial_interval_box1.insert(0, '2')
inter_trial_interval_box2 = ttk.Entry(main_frm)
inter_trial_interval_box2.insert(0, '4')
inter_trial_interval_box3 = ttk.Entry(main_frm)
inter_trial_interval_box3.insert(0, '6')
inter_trial_interval_box4 = ttk.Entry(main_frm)
inter_trial_interval_box4.insert(0, '8')

#imaging
imaging_variable = tkinter.BooleanVar() 
imaging_variable.set(False)
imaging_check = ttk.Checkbutton(main_frm, text="Imaging", var=imaging_variable)
#imaging_fps_label = ttk.Label(main_frm, text="Imaging FPS")
#imaging_fps_box = ttk.Entry(main_frm)
#imaging_fps_box.insert(0, '0')

imaging_trigger_pin_label = ttk.Label(main_frm, text="Trigger Pin No.")
imaging_trigger_pin_box = ttk.Entry(main_frm)
imaging_trigger_pin_box.insert(0, '12')

imaging_stamp_pin_label = ttk.Label(main_frm, text="Stamp Pin No.")
imaging_stamp_pin_box = ttk.Entry(main_frm)
imaging_stamp_pin_box.insert(0, '17')

imaging_2leds_variable = tkinter.BooleanVar() 
imaging_2leds_variable.set(False)
imaging_2leds_check = ttk.Checkbutton(main_frm, text="imaging w/ 2LEDs", var=imaging_2leds_variable)

imaging_led1_pin_label = ttk.Label(main_frm, text="LED1 Pin No.")
imaging_led1_pin_box = ttk.Entry(main_frm)
imaging_led1_pin_box.insert(0, '27')
imaging_led1_pin_label.bind("<1>", func=imaging_led_test)

imaging_led2_pin_label = ttk.Label(main_frm, text="LED2 Pin No.")
imaging_led2_pin_box = ttk.Entry(main_frm)
imaging_led2_pin_box.insert(0, '25')
imaging_led2_pin_label.bind("<1>", func=imaging_led_test)

focus_lens_variable = tkinter.BooleanVar() 
focus_lens_variable.set(False)
focus_lens_check = ttk.Checkbutton(main_frm, text="Focus tunable lens", var=focus_lens_variable)
focus_lens_label = ttk.Label(main_frm, text="current,current,..,wait")
focus_voltage_box = ttk.Entry(main_frm)

imaging_only_trial_label = ttk.Label(main_frm, text="if imaging only trials, pre&post time(s) from trial start",wraplength=180)
imaging_only_trial_box = ttk.Entry(main_frm)

#start, cancel button
start_button = ttk.Button(main_frm, text="Start", command=startSession)
cancel_button = ttk.Button(main_frm, text="Cancel", command=cancelSession)
save_button = ttk.Button(main_frm, text="Save", command=saveParameter)
load_button = ttk.Button(main_frm, text="Load", command=loadParameter)
camera_button = ttk.Button(main_frm, text="Camera", command=camera_start)
picamera2_variable= tkinter.BooleanVar()
picamera2_variable.set(False)
picamera2_check = ttk.Checkbutton(main_frm, text="cam2", var=picamera2_variable)
camera_crop_variable = tkinter.BooleanVar() 
camera_crop_variable.set(False)
camera_crop_check = ttk.Checkbutton(main_frm, text="Camera crop", var=camera_crop_variable)
camera_zoom_label = ttk.Label(main_frm, text="zoom")
camera_zoom_variable = tkinter.IntVar(main_frm, value=1)
camera_zoom_spin = ttk.Spinbox(main_frm, text="zoom", textvariable=camera_zoom_variable, from_=1, to=30)
#Time
estimated_time_label = ttk.Label(main_frm, text="Estimated time")
estimated_time_display = ttk.Label(main_frm, text="", font=("Arial", 12,"bold"))
elapsed_time_label = ttk.Label(main_frm, text="Elapsed time")
elapsed_time_display = ttk.Label(main_frm, text="", font=("Arial", 12,"bold"))
time_to_next_trial_display = ttk.Label(main_frm, text="", font=("Arial", 12,"bold"))
next_trial_display = ttk.Label(main_frm, text="", font=("Arial", 12,"bold"))

# body temperature
temperature_label = ttk.Label(main_frm, text="temperature")
temperature_display = ttk.Label(main_frm, text="", font=("Arial", 12,"bold"))
temperature_display["text"] = str(0)

# infrared led
infrared_led_label = ttk.Label(main_frm, text="Infrared LED Pin No.")
infrared_led_pin_box = ttk.Entry(main_frm)
infrared_led_pin_box.insert(0, '14')
infrared_led_label.bind("<1>", func=infrared_led_test)

# senser to solenoid
sensor1_to_solenoid1_variable = tkinter.BooleanVar() 
sensor1_to_solenoid1_variable.set(False)
sensor1_to_solenoid1_check = ttk.Checkbutton(main_frm, text="w/ solenoid1 (disabled)", var=sensor1_to_solenoid1_variable)

# set pin
set_pin_button = ttk.Button(main_frm, text="Set Pin", command=set_pin)

# lock parameter
lock_param_variable = tkinter.BooleanVar() 
lock_param_variable.set(False)
lock_check = ttk.Checkbutton(main_frm, text="Lock parameter", var=lock_param_variable, command=lock_param_click)

separator1 = ttk.Separator(main_frm, orient="horizontal")
separator2 = ttk.Separator(main_frm, orient="horizontal")
separator3 = ttk.Separator(main_frm, orient="horizontal")
separator4 = ttk.Separator(main_frm, orient="horizontal")
separator5 = ttk.Separator(main_frm, orient="horizontal")
separator6 = ttk.Separator(main_frm, orient="horizontal")
separator7 = ttk.Separator(main_frm, orient="horizontal")
separator8 = ttk.Separator(main_frm, orient="horizontal")
separator9 = ttk.Separator(main_frm, orient="horizontal")
separator10 = ttk.Separator(main_frm, orient="vertical")
# %% ウィジェットの配置

# ウィジェットの配置
experiment_name_label.grid(column=0, row=0, pady=0)
experiment_name_box.grid(column=1, row=0, padx=5)
file_name_label.grid(column=2, row=0, padx=5, columnspan=3)
lock_check.grid(column=4, row=0, pady=0)
#tone1について
r_tone1=1
tone1_label.grid(column=0, row=r_tone1, padx=5)
tone1_freq_label.grid(column=0, row=r_tone1+1, padx=5)
tone1_freq_box.grid(column=1, row=r_tone1+1, padx=5)
tone1_duration_label.grid(column=2, row=r_tone1+1, padx=5)
tone1_duration_box.grid(column=3, row=r_tone1+1, padx=5)
tone1_latency_label.grid(column=0, row=r_tone1+2, padx=5)
tone1_latency_box.grid(column=1, row=r_tone1+2, padx=5)
tone1_number_label.grid(column=2, row=r_tone1+2, padx=5)
tone1_number_box.grid(column=3, row=r_tone1+2, padx=5)
tone1_solenoid_check.grid(column=1, row=r_tone1, padx=5)
tone1_output_pin_label.grid(column=2, row=r_tone1, padx=5)
tone1_output_pin_box.grid(column=3, row=r_tone1, padx=5)
tone1_volume_variable_check.grid(column=4, row=r_tone1, padx=5)
tone1_volume1_box.grid(column=5, row=r_tone1, padx=5)
tone1_volume2_box.grid(column=6, row=r_tone1, padx=5)
tone1_volume3_box.grid(column=5, row=r_tone1+1, padx=5)
tone1_volume4_box.grid(column=6, row=r_tone1+1, padx=5)
tone1_volume5_box.grid(column=5, row=r_tone1+2, padx=5)
tone1_volume6_box.grid(column=6, row=r_tone1+2, padx=5)

separator1.grid(row=r_tone1+2, rowspan=2, column=0, columnspan=8, sticky="ew")

#tone2について
r_tone2=4
tone2_label.grid(column=0, row=r_tone2, padx=5)
tone2_freq_label.grid(column=0, row=r_tone2+1, padx=5)
tone2_freq_box.grid(column=1, row=r_tone2+1, padx=5)
tone2_duration_label.grid(column=2, row=r_tone2+1, padx=5)
tone2_duration_box.grid(column=3, row=r_tone2+1, padx=5)
tone2_volume_label.grid(column=4, row=r_tone2, padx=5)
tone2_volume_box.grid(column=5, row=r_tone2, padx=5)
tone2_latency_label.grid(column=0, row=r_tone2+2, padx=5)
tone2_latency_box.grid(column=1, row=r_tone2+2, padx=5)
tone2_number_label.grid(column=2, row=r_tone2+2, padx=5)
tone2_number_box.grid(column=3, row=r_tone2+2, padx=5)
tone2_solenoid_check.grid(column=1, row=r_tone2, padx=5)
tone2_output_pin_label.grid(column=2, row=r_tone2, padx=5)
tone2_output_pin_box.grid(column=3, row=r_tone2, padx=5)
tone2_led_check.grid(column=4, row=r_tone2+1, padx=5)
tone2_led_pin_label.grid(column=5, row=r_tone2+1, padx=5)
tone2_led_pin_box.grid(column=6, row=r_tone2+1, padx=5)
tone2_led_freq_label.grid(column=4, row=r_tone2+2, padx=5)
tone2_led_freq_box.grid(column=5, row=r_tone2+2, padx=5)
tone2_led_duration_label.grid(column=6, row=r_tone2+2, padx=5)
tone2_led_duration_box.grid(column=7, row=r_tone2+2, padx=5)

separator2.grid(row=r_tone2+2, rowspan=2, column=0, columnspan=8, sticky="ew")

#tone3について
r_tone3=7
tone3_label.grid(column=0, row=r_tone3, padx=5)
tone3_freq_label.grid(column=0, row=r_tone3+1, padx=5)
tone3_freq_box.grid(column=1, row=r_tone3+1, padx=5)
tone3_duration_label.grid(column=2, row=r_tone3+1, padx=5)
tone3_duration_box.grid(column=3, row=r_tone3+1, padx=5)
tone3_volume_label.grid(column=4, row=r_tone3, padx=5)
tone3_volume_box.grid(column=5, row=r_tone3, padx=5)
tone3_latency_label.grid(column=0, row=r_tone3+2, padx=5)
tone3_latency_box.grid(column=1, row=r_tone3+2, padx=5)
tone3_number_label.grid(column=2, row=r_tone3+2, padx=5)
tone3_number_box.grid(column=3, row=r_tone3+2, padx=5)
tone3_solenoid_check.grid(column=1, row=r_tone3, padx=5)
tone3_led_check.grid(column=4, row=r_tone3+1, padx=5)
tone3_led_pin_label.grid(column=5, row=r_tone3+1, padx=5)
tone3_led_pin_box.grid(column=6, row=r_tone3+1, padx=5)
tone3_led_freq_label.grid(column=4, row=r_tone3+2, padx=5)
tone3_led_freq_box.grid(column=5, row=r_tone3+2, padx=5)
tone3_led_duration_label.grid(column=6, row=r_tone3+2, padx=5)
tone3_led_duration_box.grid(column=7, row=r_tone3+2, padx=5)

tone_switch_label.grid(column=6, row=r_tone3)
tone_switch_combo.grid(column=7, row=r_tone3)

separator3.grid(row=r_tone3+2, rowspan=2, column=0, columnspan=8, sticky="ew")

#solenoid1について
r_solenoid1=10
solenoid1_label.grid(column=0, row=r_solenoid1, padx=5)
solenoid1_probability_label.grid(column=2, row=r_solenoid1, padx=5)
solenoid1_probability_box.grid(column=3, row=r_solenoid1, padx=5)
tone1_solenoid_skip_probability_label.grid(column=4, row=r_solenoid1, padx=5)
tone1_solenoid_skip_probability_box.grid(column=5, row=r_solenoid1, padx=5)
tone2_solenoid_skip_probability_label.grid(column=6, row=r_solenoid1, padx=5)
tone2_solenoid_skip_probability_box.grid(column=7, row=r_solenoid1, padx=5)
solenoid1_duration_label.grid(column=0, row=r_solenoid1+1, padx=5)
solenoid1_duration_box.grid(column=1, row=r_solenoid1+1, padx=5)
solenoid1_latency_label.grid(column=2, row=r_solenoid1+1, padx=5)
solenoid1_latency_box.grid(column=3, row=r_solenoid1+1, padx=5)
solenoid1_pin_label.grid(column=4, row=r_solenoid1+1, padx=5)
solenoid1_pin_box.grid(column=5, row=r_solenoid1+1, padx=5)
solenoid1_only_number_label.grid(column=6, row=r_solenoid1+1, padx=5)
solenoid1_only_number_box.grid(column=7, row=r_solenoid1+1, padx=5)

separator4.grid(row=r_solenoid1+1, rowspan=2, column=0, columnspan=8, sticky="ew")

#solenoid2について
r_solenoid2=12
solenoid2_probability_label.grid(column=2, row=r_solenoid2, padx=5)
solenoid2_probability_box.grid(column=3, row=r_solenoid2, padx=5)
solenoid2_label.grid(column=0, row=r_solenoid2, padx=5)
solenoid2_duration_label.grid(column=0, row=r_solenoid2+1, padx=5)
solenoid2_duration_box.grid(column=1, row=r_solenoid2+1, padx=5)
solenoid2_latency_label.grid(column=2, row=r_solenoid2+1, padx=5)
solenoid2_latency_box.grid(column=3, row=r_solenoid2+1, padx=5)
solenoid2_pin_label.grid(column=4, row=r_solenoid2+1, padx=5)
solenoid2_pin_box.grid(column=5, row=r_solenoid2+1, padx=5)
solenoid2_pulse_freq_label.grid(column=4, row=r_solenoid2, padx=5)
solenoid2_pulse_freq_box.grid(column=5, row=r_solenoid2, padx=5)
solenoid2_pulse_number_label.grid(column=6, row=r_solenoid2, padx=5)
solenoid2_pulse_number_box.grid(column=7, row=r_solenoid2, padx=5)
solenoid2_only_number_label.grid(column=6, row=r_solenoid2+1, padx=5)
solenoid2_only_number_box.grid(column=7, row=r_solenoid2+1, padx=5)

separator5.grid(row=r_solenoid2+1, rowspan=2, column=0, columnspan=8, sticky="ew")

#opto1について
r_opto1=14
opto1_label.grid(column=0, row=r_opto1, padx=5)
opto1_duration_label.grid(column=0, row=r_opto1+1, padx=5)
opto1_duration_box.grid(column=1, row=r_opto1+1, padx=5)
opto1_latency_label.grid(column=2, row=r_opto1+1, padx=5)
opto1_latency_box.grid(column=3, row=r_opto1+1, padx=5)
opto1_number_label.grid(column=2, row=r_opto1+2, padx=5)
opto1_number_box.grid(column=3, row=r_opto1+2, padx=5)
opto1_pin_label.grid(column=4, row=r_opto1+1, padx=5)
opto1_pin_box.grid(column=5, row=r_opto1+1, padx=5)

opto_max_trial_repeat_label.grid(column=6, row=r_opto1, padx=5)
opto_max_trial_repeat_box.grid(column=6, row=r_opto1+1, padx=5)

opto1_switch_label.grid(column=4, row=r_opto1+2)
opto1_switch_combo.grid(column=5, row=r_opto1+2)

separator6.grid(row=r_opto1+2, rowspan=2, column=0, columnspan=8, sticky="ew")

#opto2について
r_opto2=17
opto2_label.grid(column=0, row=r_opto2, padx=5)
opto2_duration_label.grid(column=0, row=r_opto2+1, padx=5)
opto2_duration_box.grid(column=1, row=r_opto2+1, padx=5)
opto2_latency_label.grid(column=2, row=r_opto2+1, padx=5)
opto2_latency_box.grid(column=3, row=r_opto2+1, padx=5)
opto2_number_label.grid(column=2, row=r_opto2+2, padx=5)
opto2_number_box.grid(column=3, row=r_opto2+2, padx=5)
opto2_pin_label.grid(column=4, row=r_opto2+1, padx=5)
opto2_pin_box.grid(column=5, row=r_opto2+1, padx=5)

opto2_switch_label.grid(column=4, row=r_opto2+2)
opto2_switch_combo.grid(column=5, row=r_opto2+2)

separator7.grid(row=r_opto2+2, rowspan=2, column=0, columnspan=8, sticky="ew")

#opto3について
r_opto3=20
opto3_label.grid(column=0, row=r_opto3, padx=5)
opto3_duration_label.grid(column=0, row=r_opto3+1, padx=5)
opto3_duration_box.grid(column=1, row=r_opto3+1, padx=5)
opto3_latency_label.grid(column=2, row=r_opto3+1, padx=5)
opto3_latency_box.grid(column=3, row=r_opto3+1, padx=5)
opto3_number_label.grid(column=2, row=r_opto3+2, padx=5)
opto3_number_box.grid(column=3, row=r_opto3+2, padx=5)
opto3_pin_label.grid(column=4, row=r_opto3+1, padx=5)
opto3_pin_box.grid(column=5, row=r_opto3+1, padx=5)

separator8.grid(row=r_opto3+2, rowspan=2, column=0, columnspan=8, sticky="ew")

#Sensor
r_sensor1=23
sensor1_label.grid(column=0, row=r_sensor1, padx=5)
sensor1_pin_label.grid(column=0, row=r_sensor1+1, padx=5)
sensor1_pin_box.grid(column=1, row=r_sensor1+1, padx=5)
sensor1_after_skipped_tone_window_label.grid(column=1, row=r_sensor1, padx=5)
sensor1_after_skipped_tone_window_box.grid(column=2, row=r_sensor1, padx=5)
sensor1_solenoid_block_duration_label.grid(column=3, row=r_sensor1, padx=5)
sensor1_solenoid_block_duration_box.grid(column=4, row=r_sensor1, padx=5)
# 旧仕様の「Sensor1検出で即時solenoid1」は削除したため、sensor1_to_solenoid1_checkは配置しない

# sensor2_label.grid(column=2, row=r_sensor1, padx=5)
# sensor2_pin_label.grid(column=2, row=r_sensor1+1, padx=5)
sensor2_to_tone_check.grid(column=2, row=r_sensor1+1, padx=5)
sensor2_pin_box.grid(column=3, row=r_sensor1+1, padx=5)

sensor2_to_tone_param_label.grid(column=4, row=r_sensor1+1, padx=5)
sensor2_to_tone_param_box.grid(column=5, row=r_sensor1+1, padx=5)

sensor3_to_tone_check.grid(column=2, row=r_sensor1+2, padx=5)
sensor3_pin_box.grid(column=3, row=r_sensor1+2, padx=5)

sensor3_to_tone_param_label.grid(column=4, row=r_sensor1+2, padx=5)
sensor3_to_tone_param_box.grid(column=5, row=r_sensor1+2, padx=5)

feedback_only_tone1_check.grid(column=7, row=r_sensor1, padx=5)

solenoid2_independent_check.grid(column=6, row=r_sensor1+1, padx=5)
solenoid2_session_latency_box.grid(column=6, row=r_sensor1+2, padx=5)

# #rotary encoder
# rotary_encoder_label.grid(column=4, row=r_sensor1, padx=5, pady=(20,0))
# rotary_encoder_pin_label.grid(column=4, row=r_sensor1+1, padx=5)
# rotary_encoder_pin1_box.grid(column=5, row=r_sensor1, padx=5, pady=(20,0))
# rotary_encoder_pin2_box.grid(column=5, row=r_sensor1+1, padx=5)

separator9.grid(row=r_sensor1+2, rowspan=2, column=0, columnspan=8, sticky="ew")

#trial
r_trial=25
trial_duration_label.grid(column=0, row=r_trial, padx=5)
trial_duration_box.grid(column=1, row=r_trial, padx=5)
inter_trial_interval_label.grid(column=2, row=r_trial, padx=5)
inter_trial_interval_box1.grid(column=3, row=r_trial, padx=5)
inter_trial_interval_box2.grid(column=4, row=r_trial, padx=5)
inter_trial_interval_box3.grid(column=5, row=r_trial, padx=5)
inter_trial_interval_box4.grid(column=6, row=r_trial, padx=5)
imaging_check.grid(column=0, row=r_trial+1, padx=5)
imaging_trigger_pin_label.grid(column=2, row=r_trial+1, padx=5)
imaging_trigger_pin_box.grid(column=3, row=r_trial+1, padx=5)
imaging_stamp_pin_label.grid(column=4, row=r_trial+1, padx=5)
imaging_stamp_pin_box.grid(column=5, row=r_trial+1, padx=5)

# imaging with 2LEDs
imaging_2leds_check.grid(column=6, row=r_opto2, padx=5, columnspan = 2)
imaging_led1_pin_label.grid(column=6, row=r_opto2+1, padx=5)
imaging_led1_pin_box.grid(column=7, row=r_opto2+1, padx=5)
imaging_led2_pin_label.grid(column=6, row=r_opto2+2, padx=5)
imaging_led2_pin_box.grid(column=7, row=r_opto2+2, padx=5)

# focus tunable lens
focus_lens_check.grid(column=6, row=r_opto3, padx=5, columnspan = 2)
focus_lens_label.grid(column=6, row=r_opto3+1, padx=5, columnspan = 2)
focus_voltage_box.grid(column=6, row=r_opto3+2, padx=15, columnspan = 2)

separator10.grid(row=r_opto2, rowspan=6, column=5, columnspan=2, sticky="ns")

#Button
r_button=27
start_button.grid(column=0, row=r_button, padx=5, pady=10)
cancel_button.grid(column=1, row=r_button, padx=5, pady=10)
cancel_button["state"] = "disable"
save_button.grid(column=5, row=0, padx=5, pady=0)
load_button.grid(column=6, row=0, padx=5, pady=0)
set_pin_button.grid(column=2, row=r_button+1, padx=5)

#Time
estimated_time_label.grid(column=2, row=r_button, padx=5, pady=10)
estimated_time_display.grid(column=3, row=r_button, padx=5, pady=10)
elapsed_time_label.grid(column=4, row=r_button, padx=5, pady=10)
elapsed_time_display.grid(column=5, row=r_button, padx=5, pady=10)
time_to_next_trial_display.grid(column=3, row=r_button+1, padx=5, pady=10)
next_trial_display.grid(column=3, row=r_button+2, padx=5, pady=10)

#camera
camera_button.grid(column=6, row=r_button-1, padx=5, pady=10)
picamera2_check.grid(column=7, row=r_button-1, padx=5, pady=10)
camera_crop_check.grid(column=6, row=r_button+1, padx=5, pady=0)
camera_zoom_label.grid(column=6, row=r_button, padx=5, pady=0)
camera_zoom_spin.grid(column=7, row=r_button, padx=5, pady=0)
#body temperature
temperature_label.grid(column=4, row=r_button+1, padx=5, pady=0)
temperature_display.grid(column=5, row=r_button+1, padx=5, pady=0)

#infrared led
infrared_led_label.grid(column=0, row=r_button+1, padx=5, pady=0)
infrared_led_pin_box.grid(column=1, row=r_button+1, padx=5, pady=0)

# imagingをtrial前後だけ行うかの設定
imaging_only_trial_label.grid(column=0, row=r_button+2, rowspan=2, padx=5, pady=0)
imaging_only_trial_box.grid(column=1, row=r_button+2, padx=5, pady=0)

## 配置設定
main_win.columnconfigure(0, weight=1)

#終了イベント処理
main_win.protocol("WM_DELETE_WINDOW", quit_app)

# %% 実際の実行
# ### キューをやり取りする準備
q = Queue()

# ### 音を出力する準備
SAMPLE_RATE = 44100

# PyAudio開始
p = pyaudio.PyAudio()
# ストリームを開く
stream = p.open(format=pyaudio.paFloat32, channels=1, rate=SAMPLE_RATE, frames_per_buffer=200, output=True)
# stream = p.open(format=pyaudio.paFloat32, channels=1, rate=SAMPLE_RATE, frames_per_buffer=20, output=True)
stream.get_output_latency()
# ### GPIO制御の準備
pi = pigpio.pi()

# ### センサーのイベント発生時に呼ばれる関数を準備
pi.set_mode(int(sensor1_pin_box.get()), pigpio.INPUT)
# rotary encoderの使用は停止する
# pi.set_mode(int(rotary_encoder_pin1_box.get()), pigpio.INPUT)
# pi.set_mode(int(rotary_encoder_pin2_box.get()), pigpio.INPUT)
pi.set_pull_up_down(int(sensor1_pin_box.get()), pigpio.PUD_UP)
cb = pi.callback(int(sensor1_pin_box.get()), pigpio.RISING_EDGE, event_sensor1)
cb2 = pi.callback(int(sensor1_pin_box.get()), pigpio.FALLING_EDGE, event_sensor1)
if sensor2_to_tone_variable.get():
    cb3 = pi.callback(int(sensor2_pin_box.get()), pigpio.EITHER_EDGE, event_sensor2)
# cb4 = pi.callback(int(sensor2_pin_box.get()), pigpio.FALLING_EDGE, event_sensor2)
if sensor3_to_tone_variable.get():
    cb8 = pi.callback(int(sensor3_pin_box.get()), pigpio.EITHER_EDGE, event_sensor3)
# rotary encoderの使用は停止する
# cb5 = pi.callback(int(rotary_encoder_pin1_box.get()), pigpio.RISING_EDGE, rotary_encoder_increase)
cb6 = pi.callback(int(imaging_stamp_pin_box.get()), pigpio.RISING_EDGE, event_imaging_stamp)
cb7 = pi.callback(int(imaging_stamp_pin_box.get()), pigpio.FALLING_EDGE, event_imaging_stamp)

# ### ソレノイドなどのテストをしているときにTrueになるフラグを準備
flag_solenoid1_test = False
flag_solenoid2_test = False
flag_opto1_test = False
flag_opto2_test = False
flag_opto3_test = False
flag_camera = False
flag_infrared_led_test = False
flag_imaging_led1_test = False
flag_imaging_led2_test = False

time_solenoid1_on = time.perf_counter()
time_last_lick = 0
# ### ログの出力モードの開始
logger = logging.getLogger()
logger.setLevel(logging.DEBUG)
logging.debug("pyConditioning")


# ### GUI画面を表示する
main_win.mainloop()

