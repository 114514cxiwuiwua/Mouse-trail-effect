#!/usr/bin/env python3
"""
鼠标拖尾特效 v3.1
- 光晕模式改为：连贯线条 + 多层泛光 + 头部光晕
- 点击效果：涟漪/爆发/闪光
- WH_MOUSE_LL 全局钩子
- 系统托盘 + 现代深色 GUI + 预设导入导出
- 安全退出

依赖: pip install PyQt6
用法: python mouse_trail.py
"""

import sys
import os
import json
import time
import math
import random
import queue
from collections import deque
from pathlib import Path

from PyQt6.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QHBoxLayout, QLabel,
    QPushButton, QColorDialog, QSystemTrayIcon, QMenu,
    QComboBox, QFrame, QMainWindow, QCheckBox, QFileDialog,
    QMessageBox, QGridLayout, QSlider,
)
from PyQt6.QtCore import Qt, QTimer, QPointF, QRect, pyqtSignal
from PyQt6.QtGui import (
    QPainter, QColor, QBrush, QPixmap, QIcon, QRadialGradient,
    QPainterPath, QPen, QCursor, QAction,
)

# ===== Windows 全局钩子 =====
_is_windows = (sys.platform == "win32")

if _is_windows:
    import ctypes
    import ctypes.wintypes as wt

    WH_MOUSE_LL = 14
    WM_LBUTTONDOWN = 0x0201
    WM_RBUTTONDOWN = 0x0204
    WM_MBUTTONDOWN = 0x0207

    user32 = ctypes.windll.user32
    kernel32 = ctypes.windll.kernel32

    HOOKPROC = ctypes.CFUNCTYPE(
        ctypes.c_long, ctypes.c_int, wt.WPARAM, wt.LPARAM
    )

    class MSLLHOOKSTRUCT(ctypes.Structure):
        _fields_ = [
            ("pt", wt.POINT),
            ("mouseData", wt.DWORD),
            ("flags", wt.DWORD),
            ("time", wt.DWORD),
            ("dwExtraInfo", ctypes.POINTER(ctypes.c_ulong)),
        ]


class GlobalMouseHook:
    def __init__(self, callback):
        self._callback = callback
        self._hook = None
        self._proc = None
        if not _is_windows:
            return
        self._proc = HOOKPROC(self._native_callback)
        try:
            self._hook = user32.SetWindowsHookExW(
                WH_MOUSE_LL, self._proc,
                kernel32.GetModuleHandleW(None), 0,
            )
        except Exception:
            self._hook = None

    def _native_callback(self, nCode, wParam, lParam):
        if nCode >= 0:
            if wParam in (WM_LBUTTONDOWN, WM_RBUTTONDOWN, WM_MBUTTONDOWN):
                info = ctypes.cast(
                    lParam, ctypes.POINTER(MSLLHOOKSTRUCT)
                ).contents
                self._callback(info.pt.x, info.pt.y, wParam)
        return user32.CallNextHookExW(
            self._hook, nCode, wParam, lParam
        )

    def uninstall(self):
        if self._hook:
            try:
                user32.UnhookWindowsHookEx(self._hook)
            except Exception:
                pass
            self._hook = None


# ===== 常量 =====
CONFIG_KEYS = (
    "enabled", "mode", "color", "width", "lifetime",
    "sparkle_n", "click_effect",
)

DEFAULTS = {
    "enabled": True,
    "mode": "glow",
    "color": "#00ff88",
    "width": 8,
    "lifetime": 1.0,
    "sparkle_n": 3,
    "click_effect": "ripple",
}

PRESET_COLORS = [
    "#00ff88", "#ff6b6b", "#4ecdc4", "#ffe66d", "#a855f7",
    "#3b82f6", "#ff69b4", "#ffffff", "#ff9500", "#00d4ff",
]

BUILTIN_PRESETS = {
    "霓虹绿": {
        "mode": "glow", "color": "#00ff88",
        "width": 8, "lifetime": 1.0, "sparkle_n": 3,
        "click_effect": "ripple",
    },
    "火焰红": {
        "mode": "sparkle", "color": "#ff4444",
        "width": 10, "lifetime": 0.8, "sparkle_n": 6,
        "click_effect": "burst",
    },
    "冰蓝光": {
        "mode": "glow", "color": "#00ccff",
        "width": 6, "lifetime": 1.2, "sparkle_n": 3,
        "click_effect": "flash",
    },
    "金色轨迹": {
        "mode": "line", "color": "#ffd700",
        "width": 4, "lifetime": 0.6, "sparkle_n": 3,
        "click_effect": "ripple",
    },
    "紫光星尘": {
        "mode": "sparkle", "color": "#a855f7",
        "width": 7, "lifetime": 1.5, "sparkle_n": 8,
        "click_effect": "burst",
    },
    "极简白": {
        "mode": "dots", "color": "#ffffff",
        "width": 3, "lifetime": 0.4, "sparkle_n": 2,
        "click_effect": "none",
    },
}

MODE_NAMES = {
    0: "线条 Line", 1: "圆点 Dots",
    2: "光晕 Glow", 3: "星光 Sparkle",
}
MODE_KEYS = {0: "line", 1: "dots", 2: "glow", 3: "sparkle"}
MODE_IDX = {"line": 0, "dots": 1, "glow": 2, "sparkle": 3}

CLICK_NAMES = {
    0: "无 None", 1: "涟漪 Ripple",
    2: "爆发 Burst", 3: "闪光 Flash",
}
CLICK_KEYS = {0: "none", 1: "ripple", 2: "burst", 3: "flash"}
CLICK_IDX = {"none": 0, "ripple": 1, "burst": 2, "flash": 3}


# ===== 轨迹点 =====
class TrailPoint:
    __slots__ = ("x", "y", "t")

    def __init__(self, x, y, t):
        self.x = x
        self.y = y
        self.t = t


# ===== 透明覆盖层 =====
class TrailOverlay(QWidget):

    def __init__(self, config):
        super().__init__()
        self.cfg = config
        self.pts = deque()
        self.sparks = []
        self._prev = None
        self._click_queue = queue.Queue()
        self._click_effects = []

        self.setWindowFlags(
            Qt.WindowType.FramelessWindowHint
            | Qt.WindowType.WindowStaysOnTopHint
            | Qt.WindowType.Tool
            | Qt.WindowType.WindowTransparentForInput
        )
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)

        self._offset = QPointF(0, 0)
        self._fit_screens()

        app = QApplication.instance()
        if app:
            app.screenAdded.connect(lambda _: self._fit_screens())
            app.screenRemoved.connect(lambda _: self._fit_screens())

        self._hook = GlobalMouseHook(self._on_hook_click)

        self._timer = QTimer(self, timeout=self._tick)
        self._timer.start(16)

    def _fit_screens(self):
        r = QRect()
        for s in QApplication.screens():
            r = r.united(s.geometry())
        if r.isNull():
            r = QRect(0, 0, 1920, 1080)
        self.setGeometry(r)
        self._offset = QPointF(r.topLeft())

    def _on_hook_click(self, sx, sy, button):
        self._click_queue.put((sx, sy, button))

    # ── 每帧更新 ──
    def _tick(self):
        now = time.time()

        while not self._click_queue.empty():
            try:
                sx, sy, btn = self._click_queue.get_nowait()
                lx = sx - self._offset.x()
                ly = sy - self._offset.y()
                self._create_click_effect(lx, ly, btn)
            except queue.Empty:
                break

        self._click_effects = [
            e for e in self._click_effects
            if (now - e["time"]) < e["duration"]
        ]

        gpos = QCursor.pos()
        lpos = QPointF(gpos) - self._offset

        if (
            self._prev is None
            or abs(lpos.x() - self._prev.x()) > 0.3
            or abs(lpos.y() - self._prev.y()) > 0.3
        ):
            self.pts.append(TrailPoint(lpos.x(), lpos.y(), now))
        self._prev = lpos

        life = self.cfg.get("lifetime", 1.0)
        while self.pts and (now - self.pts[0].t) > life:
            self.pts.popleft()

        if self.cfg.get("mode") == "sparkle" and self.pts:
            tail = self.pts[-1]
            for _ in range(self.cfg.get("sparkle_n", 3)):
                self.sparks.append({
                    "x": tail.x + random.uniform(-8, 8),
                    "y": tail.y + random.uniform(-8, 8),
                    "vx": random.uniform(-50, 50),
                    "vy": random.uniform(-80, -15),
                    "sz": random.uniform(1.5, 5),
                    "b": now,
                    "life": random.uniform(0.25, 0.65),
                    "hue": random.uniform(-0.06, 0.06),
                })
            self.sparks = [
                s for s in self.sparks if now - s["b"] < s["life"]
            ]
            dt = 0.016
            for s in self.sparks:
                s["x"] += s["vx"] * dt
                s["y"] += s["vy"] * dt
                s["vy"] += 130 * dt

        self.update()

    # ── 创建点击效果 ──
    def _create_click_effect(self, x, y, button):
        kind = self.cfg.get("click_effect", "ripple")
        if kind == "none":
            return
        now = time.time()
        col = self.cfg.get("color", "#00ff88")

        eff = {
            "x": x, "y": y,
            "kind": kind, "time": now, "color": col,
        }

        if kind == "ripple":
            eff["duration"] = 0.8
        elif kind == "burst":
            eff["duration"] = 0.8
            particles = []
            n = 20
            for i in range(n):
                angle = (2 * math.pi * i / n) + random.uniform(-0.2, 0.2)
                speed = random.uniform(100, 250)
                particles.append({
                    "vx": math.cos(angle) * speed,
                    "vy": math.sin(angle) * speed,
                    "sz": random.uniform(2, 5),
                    "hue": random.uniform(-0.05, 0.05),
                })
            eff["particles"] = particles
        elif kind == "flash":
            eff["duration"] = 0.5
        else:
            return

        self._click_effects.append(eff)

    # ── 绘制 ──
    def paintEvent(self, _):
        if not self.cfg.get("enabled", True):
            return
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        now = time.time()

        if self.pts:
            mode = self.cfg.get("mode", "glow")
            col = QColor(self.cfg.get("color", "#00ff88"))
            w = self.cfg.get("width", 8)
            life = self.cfg.get("lifetime", 1.0)
            n = len(self.pts)
            draw = {
                "line": self._draw_line,
                "dots": self._draw_dots,
                "glow": self._draw_glow,
                "sparkle": self._draw_sparkle,
            }.get(mode, self._draw_glow)
            draw(p, col, w, life, now, n)

        self._draw_click_effects(p, now)
        p.end()

    # ── 点击效果绘制 ──
    def _draw_click_effects(self, p, now):
        for eff in self._click_effects:
            elapsed = now - eff["time"]
            duration = eff["duration"]
            alpha = max(0.0, 1.0 - elapsed / duration)
            kind = eff["kind"]
            x = eff["x"]
            y = eff["y"]
            col = QColor(eff["color"])

            if kind == "ripple":
                self._draw_ripple(p, x, y, col, alpha, elapsed)
            elif kind == "burst":
                self._draw_burst(
                    p, x, y, col, alpha, elapsed,
                    eff.get("particles", []),
                )
            elif kind == "flash":
                self._draw_flash(p, x, y, col, alpha)

    def _draw_ripple(self, p, x, y, col, alpha, elapsed):
        max_r = self.cfg.get("width", 8) * 8
        n_rings = 3
        p.setBrush(Qt.BrushStyle.NoBrush)
        for i in range(n_rings):
            delay = i * 0.08
            t = elapsed - delay
            if t < 0:
                continue
            ring_life = 0.6
            if t > ring_life:
                continue
            progress = t / ring_life
            r = max_r * progress
            a = alpha * (1.0 - progress) * 0.7
            if a < 0.01:
                continue
            c = QColor(col)
            c.setAlphaF(a)
            pen_w = 2.5 * (1.0 - progress) + 0.5
            pen = QPen(c, pen_w)
            p.setPen(pen)
            p.drawEllipse(QPointF(x, y), r, r)

    def _draw_burst(self, p, x, y, col, alpha, elapsed, particles):
        p.setPen(Qt.PenStyle.NoPen)
        for part in particles:
            px = x + part["vx"] * elapsed
            py = y + part["vy"] * elapsed + 150 * elapsed * elapsed
            sz = part["sz"] * max(0.0, alpha)
            if sz < 0.3:
                continue
            c = QColor(col)
            c.setHsvF(
                (c.hsvHueF() + part["hue"]) % 1.0,
                c.hsvSaturationF(),
                min(1.0, c.valueF() + 0.3),
                alpha * 0.9,
            )
            p.setBrush(QBrush(c))
            p.drawEllipse(QPointF(px, py), sz, sz)

    def _draw_flash(self, p, x, y, col, alpha):
        max_r = self.cfg.get("width", 8) * 5
        r = max_r * (0.3 + 0.7 * (1.0 - alpha))
        c = QColor(col)
        c.setAlphaF(alpha * 0.5)
        grad = QRadialGradient(QPointF(x, y), max(r, 1))
        wc = QColor(255, 255, 255)
        wc.setAlphaF(alpha * 0.8)
        grad.setColorAt(0, wc)
        grad.setColorAt(0.3, c)
        grad.setColorAt(1, QColor(0, 0, 0, 0))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(grad))
        p.drawEllipse(QPointF(x, y), r, r)

    # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    #  轨迹绘制
    # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    def _draw_line(self, p, col, w, life, now, n):
        if n < 2:
            return
        pts = list(self.pts)
        for i in range(1, n):
            a = max(0.0, 1.0 - (now - pts[i].t) / life)
            prog = i / n
            width = w * prog * a
            if width < 0.3:
                continue
            c = QColor(col)
            c.setAlphaF(a * 0.92)
            pen = QPen(
                c, width, Qt.PenStyle.SolidLine,
                Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin,
            )
            p.setPen(pen)
            p.drawLine(
                QPointF(pts[i - 1].x, pts[i - 1].y),
                QPointF(pts[i].x, pts[i].y),
            )

    def _draw_dots(self, p, col, w, life, now, n):
        p.setPen(Qt.PenStyle.NoPen)
        for i, pt in enumerate(self.pts):
            a = max(0.0, 1.0 - (now - pt.t) / life)
            r = w * 0.5 * ((i + 1) / n) * a
            if r < 0.3:
                continue
            c = QColor(col)
            c.setAlphaF(a * 0.85)
            p.setBrush(QBrush(c))
            p.drawEllipse(QPointF(pt.x, pt.y), r, r)

    # ── 光晕：连贯线条 + 多层泛光 + 头部光晕 ──
    def _draw_glow(self, p, col, w, life, now, n):
        if n < 2:
            return
        pts = list(self.pts)

        # 四层叠加，由外到内：
        # (线宽倍率, 透明度系数, 是否白色核心)
        layers = [
            (5.0, 0.06, False),   # 最外层：大范围柔和光晕
            (3.2, 0.12, False),   # 第二层：中等光晕
            (1.8, 0.28, False),   # 第三层：内层光晕
            (0.3, 0.95, True),    # 最内层：亮白色核心线
        ]

        for layer_w, layer_a, is_core in layers:
            for i in range(1, n):
                a = max(0.0, 1.0 - (now - pts[i].t) / life)
                prog = i / n
                seg_w = w * prog * a * layer_w
                if seg_w < 0.3:
                    continue
                c = QColor(255, 255, 255) if is_core else QColor(col)
                c.setAlphaF(min(1.0, a * layer_a))
                pen = QPen(
                    c, seg_w, Qt.PenStyle.SolidLine,
                    Qt.PenCapStyle.RoundCap,
                    Qt.PenJoinStyle.RoundJoin,
                )
                p.setPen(pen)
                p.drawLine(
                    QPointF(pts[i - 1].x, pts[i - 1].y),
                    QPointF(pts[i].x, pts[i].y),
                )

        # 头部径向光晕（光标位置额外发光）
        head = pts[-1]
        head_a = max(0.0, 1.0 - (now - head.t) / life)
        head_r = w * 3.0
        gc = QColor(col)
        gc.setAlphaF(head_a * 0.22)
        grad = QRadialGradient(QPointF(head.x, head.y), head_r)
        grad.setColorAt(0, gc)
        mid_c = QColor(col)
        mid_c.setAlphaF(head_a * 0.08)
        grad.setColorAt(0.5, mid_c)
        grad.setColorAt(1, QColor(0, 0, 0, 0))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(grad))
        p.drawEllipse(QPointF(head.x, head.y), head_r, head_r)

    def _draw_sparkle(self, p, col, w, life, now, n):
        self._draw_line(p, col, w * 0.2, life, now, n)
        p.setPen(Qt.PenStyle.NoPen)
        for s in self.sparks:
            a = max(0.0, 1.0 - (now - s["b"]) / s["life"])
            sz = s["sz"] * a
            if sz < 0.3:
                continue
            c = QColor(col)
            c.setHsvF(
                (c.hsvHueF() + s["hue"]) % 1.0,
                c.hsvSaturationF(),
                min(1.0, c.valueF() + 0.25), a,
            )
            p.setBrush(QBrush(c))
            p.save()
            p.translate(s["x"], s["y"])
            p.rotate(s["b"] * 500 % 360)
            path = QPainterPath()
            for j in range(4):
                ang = j * math.pi / 2
                ox = math.cos(ang) * sz
                oy = math.sin(ang) * sz
                ia = ang + math.pi / 4
                ix = math.cos(ia) * sz * 0.28
                iy = math.sin(ia) * sz * 0.28
                if j == 0:
                    path.moveTo(ox, oy)
                else:
                    path.lineTo(ox, oy)
                path.lineTo(ix, iy)
            path.closeSubpath()
            p.drawPath(path)
            p.restore()

    def shutdown(self):
        self._timer.stop()
        if self._hook:
            self._hook.uninstall()
        self.hide()
        self.deleteLater()


# ===== 自定义滑块 =====
class ModernSlider(QWidget):
    valueChanged = pyqtSignal(int)

    def __init__(self, label, lo, hi, default, suffix="", factor=1.0, parent=None):
        super().__init__(parent)
        self._factor = factor
        self._suffix = suffix
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(12)

        self._lbl = QLabel(label)
        self._lbl.setFixedWidth(64)
        lay.addWidget(self._lbl)

        self._slider = QSlider(Qt.Orientation.Horizontal)
        self._slider.setMinimum(lo)
        self._slider.setMaximum(hi)
        self._slider.setValue(default)
        self._slider.valueChanged.connect(self._on_change)
        lay.addWidget(self._slider, 1)

        self._val = QLabel(self._fmt(default))
        self._val.setFixedWidth(50)
        align = Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter
        self._val.setAlignment(align)
        lay.addWidget(self._val)

    def _fmt(self, v):
        if self._factor != 1.0:
            return str(round(v * self._factor, 1)) + self._suffix
        return str(v) + self._suffix

    def _on_change(self, v):
        self._val.setText(self._fmt(v))
        self.valueChanged.emit(v)

    def value(self):
        return self._slider.value()

    def setValue(self, v):
        self._slider.setValue(v)


# ===== 颜色按钮 =====
class ColorButton(QPushButton):
    colorChanged = pyqtSignal(str)

    def __init__(self, color="#00ff88", parent=None):
        super().__init__(parent)
        self._c = color
        self.setFixedSize(36, 36)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.clicked.connect(self._pick)
        self._refresh()

    def _refresh(self):
        s = "QPushButton{background:" + self._c
        s += ";border:2px solid rgba(255,255,255,.15);border-radius:18px}"
        s += "QPushButton:hover{border:2px solid rgba(255,255,255,.5)}"
        self.setStyleSheet(s)

    def _pick(self):
        c = QColorDialog.getColor(QColor(self._c), self, "选择颜色")
        if c.isValid():
            self._c = c.name()
            self._refresh()
            self.colorChanged.emit(self._c)

    def color(self):
        return self._c

    def setColor(self, c):
        self._c = c
        self._refresh()


# ===== 设置窗口 =====
class SettingsWindow(QMainWindow):
    def __init__(self, config):
        super().__init__()
        self.cfg = config
        self.setWindowTitle("鼠标拖尾 - 设置")
        self.setFixedSize(460, 780)
        flags = Qt.WindowType.Window | Qt.WindowType.WindowStaysOnTopHint
        self.setWindowFlags(flags)
        self._build_ui()
        self._apply_qss()

    def _sep(self):
        f = QFrame()
        f.setFrameShape(QFrame.Shape.HLine)
        f.setObjectName("sep")
        return f

    def _build_ui(self):
        root = QWidget()
        self.setCentralWidget(root)
        lay = QVBoxLayout(root)
        lay.setContentsMargins(28, 20, 28, 16)
        lay.setSpacing(10)

        title = QLabel("鼠标拖尾效果")
        title.setObjectName("title")
        lay.addWidget(title)
        sub = QLabel("自定义光标轨迹 + 点击效果")
        sub.setObjectName("subtitle")
        lay.addWidget(sub)
        lay.addWidget(self._sep())

        # 启用
        row = QHBoxLayout()
        lbl = QLabel("启用效果")
        lbl.setObjectName("fieldLabel")
        self._chk = QCheckBox()
        self._chk.setChecked(self.cfg.get("enabled", True))
        self._chk.stateChanged.connect(self._on_toggle)
        row.addWidget(lbl)
        row.addStretch()
        row.addWidget(self._chk)
        lay.addLayout(row)
        lay.addWidget(self._sep())

        # 内置预设
        lbl_p = QLabel("内置预设")
        lbl_p.setObjectName("fieldLabel")
        lay.addWidget(lbl_p)
        grid = QGridLayout()
        grid.setSpacing(6)
        preset_list = list(BUILTIN_PRESETS.items())
        for idx in range(len(preset_list)):
            name = preset_list[idx][0]
            preset = preset_list[idx][1]
            b = QPushButton(name)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setObjectName("presetBtn")
            b.clicked.connect(lambda _, p=preset: self._apply_preset(p))
            grid.addWidget(b, idx // 3, idx % 3)
        lay.addLayout(grid)
        lay.addWidget(self._sep())

        # 轨迹模式
        lbl2 = QLabel("轨迹模式")
        lbl2.setObjectName("fieldLabel")
        lay.addWidget(lbl2)
        self._mode = QComboBox()
        self._mode.addItems(list(MODE_NAMES.values()))
        cur = MODE_IDX.get(self.cfg.get("mode", "glow"), 2)
        self._mode.setCurrentIndex(cur)
        self._mode.currentIndexChanged.connect(
            lambda i: self.cfg.__setitem__("mode", MODE_KEYS.get(i, "glow"))
        )
        lay.addWidget(self._mode)
        desc = QLabel(
            "线条: 实线轨迹 | 圆点: 粒子珠串 | "
            "光晕: 泛光线条 | 星光: 闪烁粒子"
        )
        desc.setObjectName("desc")
        desc.setWordWrap(True)
        lay.addWidget(desc)
        lay.addWidget(self._sep())

        # 点击效果
        lbl4 = QLabel("点击效果")
        lbl4.setObjectName("fieldLabel")
        lay.addWidget(lbl4)
        self._click_combo = QComboBox()
        self._click_combo.addItems(list(CLICK_NAMES.values()))
        click_cur = CLICK_IDX.get(self.cfg.get("click_effect", "ripple"), 1)
        self._click_combo.setCurrentIndex(click_cur)
        self._click_combo.currentIndexChanged.connect(
            lambda i: self.cfg.__setitem__(
                "click_effect", CLICK_KEYS.get(i, "none")
            )
        )
        lay.addWidget(self._click_combo)
        click_desc = QLabel(
            "涟漪: 扩散环 | 爆发: 粒子飞散 | 闪光: 径向光晕 | 无: 关闭"
        )
        click_desc.setObjectName("desc")
        lay.addWidget(click_desc)
        lay.addWidget(self._sep())

        # 颜色
        lbl3 = QLabel("颜色")
        lbl3.setObjectName("fieldLabel")
        lay.addWidget(lbl3)
        color_row = QHBoxLayout()
        color_row.setSpacing(8)
        self._cbtn = ColorButton(self.cfg.get("color", "#00ff88"))
        self._cbtn.colorChanged.connect(
            lambda c: self.cfg.__setitem__("color", c)
        )
        color_row.addWidget(self._cbtn)
        for pc in PRESET_COLORS:
            b = QPushButton()
            b.setFixedSize(24, 24)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            style = "QPushButton{background:" + pc
            style += ";border:2px solid transparent;border-radius:12px}"
            style += "QPushButton:hover{border:2px solid #fff}"
            b.setStyleSheet(style)
            b.clicked.connect(lambda _, c=pc: self._cbtn.setColor(c))
            color_row.addWidget(b)
        color_row.addStretch()
        lay.addLayout(color_row)
        lay.addWidget(self._sep())

        # 滑块
        self._w_slider = ModernSlider(
            "宽度", 1, 30, self.cfg.get("width", 8), "px"
        )
        self._w_slider.valueChanged.connect(
            lambda v: self.cfg.__setitem__("width", v)
        )
        lay.addWidget(self._w_slider)

        default_life = int(self.cfg.get("lifetime", 1.0) * 100)
        self._l_slider = ModernSlider(
            "持续", 10, 300, default_life, "s", 0.01
        )
        self._l_slider.valueChanged.connect(
            lambda v: self.cfg.__setitem__("lifetime", v / 100.0)
        )
        lay.addWidget(self._l_slider)

        self._s_slider = ModernSlider(
            "星光数", 1, 10, self.cfg.get("sparkle_n", 3)
        )
        self._s_slider.valueChanged.connect(
            lambda v: self.cfg.__setitem__("sparkle_n", v)
        )
        lay.addWidget(self._s_slider)
        lay.addWidget(self._sep())

        # 导入导出
        lbl_io = QLabel("预设管理")
        lbl_io.setObjectName("fieldLabel")
        lay.addWidget(lbl_io)
        io_row = QHBoxLayout()
        io_row.setSpacing(10)
        imp = QPushButton("导入预设")
        imp.setObjectName("accentBtn")
        imp.setCursor(Qt.CursorShape.PointingHandCursor)
        imp.clicked.connect(self._import_preset)
        io_row.addWidget(imp)
        exp = QPushButton("导出预设")
        exp.setObjectName("accentBtn")
        exp.setCursor(Qt.CursorShape.PointingHandCursor)
        exp.clicked.connect(self._export_preset)
        io_row.addWidget(exp)
        lay.addLayout(io_row)
        lay.addWidget(self._sep())

        # 底部
        btn_row = QHBoxLayout()
        btn_row.setSpacing(10)
        reset = QPushButton("重置默认")
        reset.setCursor(Qt.CursorShape.PointingHandCursor)
        reset.clicked.connect(self._reset_defaults)
        hide_btn = QPushButton("最小化到托盘")
        hide_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        hide_btn.clicked.connect(self.hide)
        btn_row.addWidget(reset)
        btn_row.addWidget(hide_btn)
        lay.addLayout(btn_row)

        lay.addStretch()
        tip = QLabel("双击托盘图标打开设置 | 右键托盘查看更多")
        tip.setObjectName("tip")
        tip.setAlignment(Qt.AlignmentFlag.AlignCenter)
        lay.addWidget(tip)

    def _on_toggle(self, state):
        self.cfg["enabled"] = (state == Qt.CheckState.Checked.value)

    def _apply_preset(self, preset):
        for k in CONFIG_KEYS:
            if k in preset:
                self.cfg[k] = preset[k]
        self._sync_ui()

    def _sync_ui(self):
        self._chk.setChecked(self.cfg.get("enabled", True))
        idx = MODE_IDX.get(self.cfg.get("mode", "glow"), 2)
        self._mode.setCurrentIndex(idx)
        self._cbtn.setColor(self.cfg.get("color", "#00ff88"))
        self._w_slider.setValue(self.cfg.get("width", 8))
        life_val = int(self.cfg.get("lifetime", 1.0) * 100)
        self._l_slider.setValue(life_val)
        self._s_slider.setValue(self.cfg.get("sparkle_n", 3))
        click_idx = CLICK_IDX.get(self.cfg.get("click_effect", "ripple"), 1)
        self._click_combo.setCurrentIndex(click_idx)

    def _reset_defaults(self):
        self.cfg.update(DEFAULTS.copy())
        self._sync_ui()

    def _import_preset(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "导入预设", "",
            "JSON 预设 (*.json);;所有文件 (*)"
        )
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            settings = data.get("settings", data)
            for k in CONFIG_KEYS:
                if k in settings:
                    self.cfg[k] = settings[k]
            self._sync_ui()
            name = os.path.basename(path)
            QMessageBox.information(
                self, "导入成功", "预设已导入: " + name
            )
        except Exception as e:
            QMessageBox.warning(
                self, "导入失败", "无法解析: " + str(e)
            )

    def _export_preset(self):
        path, _ = QFileDialog.getSaveFileName(
            self, "导出预设", "my_preset.json",
            "JSON 预设 (*.json);;所有文件 (*)"
        )
        if not path:
            return
        data = {"name": Path(path).stem, "version": 1, "settings": {}}
        for k in CONFIG_KEYS:
            data["settings"][k] = self.cfg.get(k, DEFAULTS.get(k))
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            QMessageBox.information(
                self, "导出成功", "预设已保存: " + path
            )
        except Exception as e:
            QMessageBox.warning(
                self, "导出失败", "无法保存: " + str(e)
            )

    def closeEvent(self, e):
        e.ignore()
        self.hide()

    def _apply_qss(self):
        qss = []
        qss.append("QMainWindow, QWidget { background: #0c0c1d; }")
        qss.append("#title { font-size: 20px; font-weight: 700; color: #f0f0f0; border: none; background: none; }")
        qss.append("#subtitle { font-size: 12px; color: #555; border: none; background: none; }")
        qss.append("#fieldLabel { font-size: 12px; color: #777; font-weight: 600; border: none; background: none; }")
        qss.append("#desc { font-size: 11px; color: #444; border: none; background: none; }")
        qss.append("#tip { font-size: 10px; color: #333; border: none; background: none; }")
        qss.append("QFrame#sep { color: #1a1a30; border: none; background: none; max-height: 1px; }")
        qss.append("QPushButton#presetBtn { background: #161630; color: #aaa; border: 1px solid #252545; border-radius: 6px; padding: 7px 4px; font-size: 12px; }")
        qss.append("QPushButton#presetBtn:hover { background: #1e1e42; border-color: #00ff88; color: #fff; }")
        qss.append("QPushButton#accentBtn { background: #0d2e1a; color: #00ff88; border: 1px solid #00ff8844; border-radius: 8px; padding: 10px 16px; font-size: 13px; font-weight: 600; }")
        qss.append("QPushButton#accentBtn:hover { background: #0f3d22; border-color: #00ff88; }")
        qss.append("QComboBox { background: #141430; color: #ddd; border: 1px solid #252545; border-radius: 8px; padding: 8px 14px; font-size: 13px; }")
        qss.append("QComboBox:hover { border-color: #4a4a80; }")
        qss.append("QComboBox::drop-down { border: none; width: 28px; }")
        qss.append("QComboBox QAbstractItemView { background: #141430; color: #ddd; border: 1px solid #252545; selection-background-color: #0f3460; border-radius: 6px; padding: 4px; }")
        qss.append("QCheckBox { spacing: 8px; }")
        qss.append("QCheckBox::indicator { width: 42px; height: 22px; border-radius: 11px; background: #252545; }")
        qss.append("QCheckBox::indicator:checked { background: #00ff88; }")
        qss.append("QCheckBox::indicator:hover { background: #3a3a5c; }")
        qss.append("QSlider::groove:horizontal { height: 4px; background: #252545; border-radius: 2px; }")
        qss.append("QSlider::handle:horizontal { background: #00ff88; width: 16px; height: 16px; margin: -6px 0; border-radius: 8px; }")
        qss.append("QSlider::handle:horizontal:hover { background: #33ffaa; }")
        qss.append("QSlider::sub-page:horizontal { background: #00cc6a; border-radius: 2px; }")
        qss.append("QPushButton { background: #161630; color: #999; border: 1px solid #252545; border-radius: 8px; padding: 10px 18px; font-size: 13px; }")
        qss.append("QPushButton:hover { background: #1e1e3c; border-color: #4a4a80; color: #fff; }")
        qss.append("QPushButton:pressed { background: #0e0e22; }")
        qss.append("QLabel { color: #999; font-size: 13px; border: none; background: none; }")
        self.setStyleSheet("\n".join(qss))


# ===== 主控制器 =====
class MouseTrailApp:

    def __init__(self):
        self.app = QApplication(sys.argv)
        self.app.setQuitOnLastWindowClosed(False)
        self.config = DEFAULTS.copy()
        self._exiting = False

        self.overlay = TrailOverlay(self.config)
        self.overlay.show()

        self.settings = SettingsWindow(self.config)

        self._setup_tray()

        self.app.aboutToQuit.connect(self._cleanup)

    def _setup_tray(self):
        pm = QPixmap(64, 64)
        pm.fill(QColor(0, 0, 0, 0))
        painter = QPainter(pm)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(QColor("#00ff88"))
        painter.drawEllipse(4, 4, 56, 56)
        painter.setBrush(QColor("#0c0c1d"))
        painter.drawEllipse(12, 12, 40, 40)
        painter.setBrush(QColor("#ffffff"))
        painter.drawEllipse(24, 24, 16, 16)
        painter.end()

        self.tray = QSystemTrayIcon(QIcon(pm), self.app)

        menu = QMenu()
        ms = "QMenu{background:#141430;color:#ddd;border:1px solid #252545;border-radius:6px;padding:4px}"
        ms += "QMenu::item{padding:8px 28px;border-radius:4px}"
        ms += "QMenu::item:selected{background:#0f3460}"
        ms += "QMenu::separator{height:1px;background:#252545;margin:4px 8px}"
        menu.setStyleSheet(ms)

        self._toggle_act = QAction("暂停效果", self.app)
        self._toggle_act.triggered.connect(self._toggle)
        menu.addAction(self._toggle_act)

        settings_act = QAction("打开设置", self.app)
        settings_act.triggered.connect(self._show_settings)
        menu.addAction(settings_act)

        menu.addSeparator()

        quit_act = QAction("安全退出", self.app)
        quit_act.triggered.connect(self._quit)
        menu.addAction(quit_act)

        self.tray.setContextMenu(menu)
        self.tray.activated.connect(self._on_activated)
        self.tray.setToolTip("鼠标拖尾 - 运行中")
        self.tray.show()

    def _toggle(self):
        self.config["enabled"] = not self.config["enabled"]
        if self.config["enabled"]:
            self.overlay.show()
            self._toggle_act.setText("暂停效果")
            self.tray.setToolTip("鼠标拖尾 - 运行中")
        else:
            self.overlay.hide()
            self._toggle_act.setText("恢复效果")
            self.tray.setToolTip("鼠标拖尾 - 已暂停")
        self.settings._sync_ui()

    def _show_settings(self):
        self.settings._sync_ui()
        self.settings.show()
        self.settings.raise_()
        self.settings.activateWindow()

    def _on_activated(self, reason):
        if reason == QSystemTrayIcon.ActivationReason.DoubleClick:
            self._show_settings()

    def _quit(self):
        if self._exiting:
            return
        self._exiting = True
        self._cleanup()
        self.app.quit()

    def _cleanup(self):
        try:
            self.overlay.shutdown()
        except Exception:
            pass
        try:
            self.tray.hide()
        except Exception:
            pass
        try:
            self.settings.close()
        except Exception:
            pass

    def run(self):
        return self.app.exec()


# ===== 入口 =====
if __name__ == "__main__":
    app = MouseTrailApp()
    sys.exit(app.run())
