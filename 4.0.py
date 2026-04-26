#!/usr/bin/env python3
"""Mouse Trail v4.2"""

import sys
import os
import json
import time
import math
import random
from collections import deque

from PyQt6.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QHBoxLayout, QLabel,
    QPushButton, QColorDialog, QSystemTrayIcon, QMenu,
    QComboBox, QFrame, QMainWindow, QCheckBox, QFileDialog,
    QMessageBox, QSlider, QLineEdit,
)
from PyQt6.QtCore import Qt, QTimer, QPointF, QRect, pyqtSignal
from PyQt6.QtGui import (
    QPainter, QColor, QBrush, QPixmap, QIcon, QRadialGradient,
    QPainterPath, QPen, QCursor, QAction,
)

_win = sys.platform == "win32"
if _win:
    import ctypes

_CFG = os.path.join(os.path.expanduser("~"), ".mouse_trail.json")
_KEYS = (
    "enabled", "mode", "color", "width",
    "lifetime", "sparkle_n", "click_effect",
)
DEFAULTS = {
    "enabled": True, "mode": "glow", "color": "#00ff88",
    "width": 8, "lifetime": 1.0, "sparkle_n": 3,
    "click_effect": "ripple",
}
_COLORS = [
    "#00ff88", "#ff6b6b", "#4ecdc4", "#ffe66d",
    "#a855f7", "#3b82f6", "#ff69b4", "#ffffff",
    "#ff9500", "#00d4ff",
]
MIDX = {"line": 0, "dots": 1, "glow": 2, "sparkle": 3}
CIDX = {"none": 0, "ripple": 1, "burst": 2, "flash": 3}
MKEY = {0: "line", 1: "dots", 2: "glow", 3: "sparkle"}
CKEY = {0: "none", 1: "ripple", 2: "burst", 3: "flash"}

_TR = {
    "zh": {
        "title": "鼠标拖尾效果",
        "subtitle": "自定义光标轨迹 + 点击效果",
        "enable": "启用效果",
        "trail_mode": "轨迹模式",
        "click_effect": "点击效果",
        "color": "颜色",
        "width": "宽度",
        "duration": "持续",
        "sparkles": "星光数",
        "preset_mgr": "预设管理",
        "preset_name": "输入预设名称",
        "save": "保存",
        "load": "加载",
        "delete": "删除",
        "import_f": "导入",
        "export_f": "导出",
        "reset": "重置默认",
        "minimize": "最小化到托盘",
        "tip": "双击托盘图标打开设置",
        "tray_run": "鼠标拖尾 - 运行中",
        "tray_pause": "鼠标拖尾 - 已暂停",
        "pause": "暂停效果",
        "resume": "恢复效果",
        "open_set": "打开设置",
        "exit": "安全退出",
        "lang": "语言",
        "m0": "线条", "m1": "圆点", "m2": "光晕", "m3": "星光",
        "mode_desc": "线条: 实线 | 圆点: 珠串 | 光晕: 泛光线 | 星光: 闪烁",
        "c0": "无", "c1": "涟漪", "c2": "爆发", "c3": "闪光",
        "click_desc": "涟漪: 扩散环 | 爆发: 飞散 | 闪光: 光晕 | 无: 关闭",
        "saved": "已保存",
        "loaded": "已加载",
        "deleted": "已删除",
        "err_name": "请输入预设名称",
        "ow": "预设已存在，覆盖？",
        "del_confirm": "确认删除此预设？",
        "import_ok": "导入成功",
        "export_ok": "导出成功",
    },
    "en": {
        "title": "Mouse Trail",
        "subtitle": "Custom cursor trail + click effects",
        "enable": "Enable",
        "trail_mode": "Trail Mode",
        "click_effect": "Click Effect",
        "color": "Color",
        "width": "Width",
        "duration": "Duration",
        "sparkles": "Sparkles",
        "preset_mgr": "Presets",
        "preset_name": "Preset name",
        "save": "Save",
        "load": "Load",
        "delete": "Delete",
        "import_f": "Import",
        "export_f": "Export",
        "reset": "Reset",
        "minimize": "Minimize",
        "tip": "Double-click tray icon to open settings",
        "tray_run": "Trail - Running",
        "tray_pause": "Trail - Paused",
        "pause": "Pause",
        "resume": "Resume",
        "open_set": "Settings",
        "exit": "Exit",
        "lang": "Language",
        "m0": "Line", "m1": "Dots", "m2": "Glow", "m3": "Sparkle",
        "mode_desc": "Line: solid | Dots: chain | Glow: neon | Sparkle: glitter",
        "c0": "None", "c1": "Ripple", "c2": "Burst", "c3": "Flash",
        "click_desc": "Ripple: rings | Burst: scatter | Flash: glow | None: off",
        "saved": "Saved",
        "loaded": "Loaded",
        "deleted": "Deleted",
        "err_name": "Enter a preset name",
        "ow": "Preset exists. Overwrite?",
        "del_confirm": "Delete this preset?",
        "import_ok": "Imported",
        "export_ok": "Exported",
    },
}
_lang = ["zh"]


def T(k):
    return _TR.get(_lang[0], _TR["zh"]).get(k, k)


def load_file():
    try:
        with open(_CFG, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return None


def save_file(cfg, presets, lang):
    try:
        with open(_CFG, "w", encoding="utf-8") as f:
            json.dump(
                {"language": lang, "settings": cfg, "presets": presets},
                f, ensure_ascii=False, indent=2,
            )
    except Exception:
        pass


class TP:
    __slots__ = ("x", "y", "t")

    def __init__(self, x, y, t):
        self.x = x
        self.y = y
        self.t = t


# ============================================================
#  Overlay
# ============================================================
class Overlay(QWidget):
    def __init__(self, cfg):
        super().__init__()
        self.cfg = cfg
        self.pts = deque()
        self.sparks = []
        self._prev = None
        self._btns = {}
        self._clicks = []

        self.setWindowFlags(
            Qt.WindowType.FramelessWindowHint
            | Qt.WindowType.WindowStaysOnTopHint
            | Qt.WindowType.Tool
            | Qt.WindowType.WindowTransparentForInput
        )
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)

        self._off = QPointF(0, 0)
        self._fit()
        app = QApplication.instance()
        if app:
            app.screenAdded.connect(lambda _: self._fit())
            app.screenRemoved.connect(lambda _: self._fit())

        self._tmr = QTimer(self, timeout=self._tick)
        self._tmr.start(16)

    def _fit(self):
        r = QRect()
        for s in QApplication.screens():
            r = r.united(s.geometry())
        if r.isNull():
            r = QRect(0, 0, 1920, 1080)
        self.setGeometry(r)
        self._off = QPointF(r.topLeft())

    def _tick(self):
        now = time.time()

        if _win:
            u32 = ctypes.windll.user32
            for vk in (0x01, 0x02, 0x04):
                down = bool(u32.GetAsyncKeyState(vk) & 0x8000)
                if down and not self._btns.get(vk, False):
                    pos = QCursor.pos()
                    self._mk_click(
                        pos.x() - self._off.x(),
                        pos.y() - self._off.y(),
                    )
                self._btns[vk] = down

        self._clicks = [c for c in self._clicks if now - c["t"] < c["d"]]

        gp = QCursor.pos()
        lp = QPointF(gp) - self._off
        if (
            self._prev is None
            or abs(lp.x() - self._prev.x()) > 0.3
            or abs(lp.y() - self._prev.y()) > 0.3
        ):
            self.pts.append(TP(lp.x(), lp.y(), now))
        self._prev = lp

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
            self.sparks = [s for s in self.sparks if now - s["b"] < s["life"]]
            dt = 0.016
            for s in self.sparks:
                s["x"] += s["vx"] * dt
                s["y"] += s["vy"] * dt
                s["vy"] += 130 * dt

        self.update()

    def _mk_click(self, x, y):
        kind = self.cfg.get("click_effect", "ripple")
        if kind == "none":
            return
        now = time.time()
        col = self.cfg.get("color", "#00ff88")
        c = {"x": x, "y": y, "kind": kind, "t": now, "color": col}
        if kind == "ripple":
            c["d"] = 0.8
        elif kind == "burst":
            c["d"] = 0.8
            ps = []
            for i in range(20):
                a = 2 * math.pi * i / 20 + random.uniform(-0.2, 0.2)
                sp = random.uniform(100, 250)
                ps.append({
                    "vx": math.cos(a) * sp,
                    "vy": math.sin(a) * sp,
                    "sz": random.uniform(2, 5),
                    "hu": random.uniform(-0.05, 0.05),
                })
            c["ps"] = ps
        elif kind == "flash":
            c["d"] = 0.5
        else:
            return
        self._clicks.append(c)

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
            fn = {
                "line": self._dr_line,
                "dots": self._dr_dots,
                "glow": self._dr_glow,
                "sparkle": self._dr_sparkle,
            }.get(mode, self._dr_glow)
            fn(p, col, w, life, now, n)

        self._dr_clicks(p, now)
        p.end()

    def _dr_clicks(self, p, now):
        for e in self._clicks:
            el = now - e["t"]
            a = max(0.0, 1 - el / e["d"])
            k = e["kind"]
            x, y = e["x"], e["y"]
            col = QColor(e["color"])
            if k == "ripple":
                self._dr_ripple(p, x, y, col, a, el)
            elif k == "burst":
                self._dr_burst(p, x, y, col, a, el, e.get("ps", []))
            elif k == "flash":
                self._dr_flash(p, x, y, col, a)

    def _dr_ripple(self, p, x, y, col, a, el):
        mx = self.cfg.get("width", 8) * 8
        p.setBrush(Qt.BrushStyle.NoBrush)
        for i in range(3):
            t = el - i * 0.08
            if t < 0 or t > 0.6:
                continue
            pr = t / 0.6
            r = mx * pr
            al = a * (1 - pr) * 0.7
            if al < 0.01:
                continue
            c = QColor(col)
            c.setAlphaF(al)
            p.setPen(QPen(c, 2.5 * (1 - pr) + 0.5))
            p.drawEllipse(QPointF(x, y), r, r)

    def _dr_burst(self, p, x, y, col, a, el, ps):
        p.setPen(Qt.PenStyle.NoPen)
        for pt in ps:
            px = x + pt["vx"] * el
            py = y + pt["vy"] * el + 150 * el * el
            sz = pt["sz"] * max(0.0, a)
            if sz < 0.3:
                continue
            c = QColor(col)
            c.setHsvF(
                (c.hsvHueF() + pt["hu"]) % 1.0,
                c.hsvSaturationF(),
                min(1.0, c.valueF() + 0.3),
                a * 0.9,
            )
            p.setBrush(QBrush(c))
            p.drawEllipse(QPointF(px, py), sz, sz)

    def _dr_flash(self, p, x, y, col, a):
        mx = self.cfg.get("width", 8) * 5
        r = mx * (0.3 + 0.7 * (1 - a))
        c = QColor(col)
        c.setAlphaF(a * 0.5)
        g = QRadialGradient(QPointF(x, y), max(r, 1))
        w = QColor(255, 255, 255)
        w.setAlphaF(a * 0.8)
        g.setColorAt(0, w)
        g.setColorAt(0.3, c)
        g.setColorAt(1, QColor(0, 0, 0, 0))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(g))
        p.drawEllipse(QPointF(x, y), r, r)

    def _dr_line(self, p, col, w, life, now, n):
        if n < 2:
            return
        pts = list(self.pts)
        for i in range(1, n):
            a = max(0.0, 1 - (now - pts[i].t) / life)
            wd = w * (i / n) * a
            if wd < 0.3:
                continue
            c = QColor(col)
            c.setAlphaF(a * 0.92)
            pen = QPen(c, wd, Qt.PenStyle.SolidLine,
                       Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin)
            p.setPen(pen)
            p.drawLine(
                QPointF(pts[i - 1].x, pts[i - 1].y),
                QPointF(pts[i].x, pts[i].y),
            )

    def _dr_dots(self, p, col, w, life, now, n):
        p.setPen(Qt.PenStyle.NoPen)
        for i, pt in enumerate(self.pts):
            a = max(0.0, 1 - (now - pt.t) / life)
            r = w * 0.5 * ((i + 1) / n) * a
            if r < 0.3:
                continue
            c = QColor(col)
            c.setAlphaF(a * 0.85)
            p.setBrush(QBrush(c))
            p.drawEllipse(QPointF(pt.x, pt.y), r, r)

    def _dr_glow(self, p, col, w, life, now, n):
        if n < 2:
            return
        pts = list(self.pts)
        layers = [
            (5.0, 0.06, False),
            (3.2, 0.12, False),
            (1.8, 0.28, False),
            (0.3, 0.95, True),
        ]
        for lw, la, core in layers:
            for i in range(1, n):
                a = max(0.0, 1 - (now - pts[i].t) / life)
                wd = w * (i / n) * a * lw
                if wd < 0.3:
                    continue
                c = QColor(255, 255, 255) if core else QColor(col)
                c.setAlphaF(min(1.0, a * la))
                pen = QPen(c, wd, Qt.PenStyle.SolidLine,
                           Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin)
                p.setPen(pen)
                p.drawLine(
                    QPointF(pts[i - 1].x, pts[i - 1].y),
                    QPointF(pts[i].x, pts[i].y),
                )
        hd = pts[-1]
        ha = max(0.0, 1 - (now - hd.t) / life)
        hr = w * 3.0
        gc = QColor(col)
        gc.setAlphaF(ha * 0.22)
        g = QRadialGradient(QPointF(hd.x, hd.y), hr)
        g.setColorAt(0, gc)
        mc = QColor(col)
        mc.setAlphaF(ha * 0.08)
        g.setColorAt(0.5, mc)
        g.setColorAt(1, QColor(0, 0, 0, 0))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(g))
        p.drawEllipse(QPointF(hd.x, hd.y), hr, hr)

    def _dr_sparkle(self, p, col, w, life, now, n):
        self._dr_line(p, col, w * 0.2, life, now, n)
        p.setPen(Qt.PenStyle.NoPen)
        for s in self.sparks:
            a = max(0.0, 1 - (now - s["b"]) / s["life"])
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
        self._tmr.stop()
        self.hide()
        self.deleteLater()


# ============================================================
#  UI widgets
# ============================================================
class MSlider(QWidget):
    valChanged = pyqtSignal(int)

    def __init__(self, label, lo, hi, default, suffix="", factor=1.0, parent=None):
        super().__init__(parent)
        self._factor = factor
        self._suffix = suffix
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(12)
        self.lbl = QLabel(label)
        self.lbl.setFixedWidth(64)
        lay.addWidget(self.lbl)
        self.sl = QSlider(Qt.Orientation.Horizontal)
        self.sl.setMinimum(lo)
        self.sl.setMaximum(hi)
        self.sl.setValue(default)
        self.sl.valueChanged.connect(self._chg)
        lay.addWidget(self.sl, 1)
        self.vl = QLabel(self._fmt(default))
        self.vl.setFixedWidth(50)
        self.vl.setAlignment(
            Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter
        )
        lay.addWidget(self.vl)

    def _fmt(self, v):
        if self._factor != 1.0:
            return str(round(v * self._factor, 1)) + self._suffix
        return str(v) + self._suffix

    def _chg(self, v):
        self.vl.setText(self._fmt(v))
        self.valChanged.emit(v)

    def setVal(self, v):
        self.sl.setValue(v)


class CBtn(QPushButton):
    colorChanged = pyqtSignal(str)

    def __init__(self, color="#00ff88", parent=None):
        super().__init__(parent)
        self._c = color
        self.setFixedSize(36, 36)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.clicked.connect(self._pick)
        self._rfr()

    def _rfr(self):
        self.setStyleSheet(
            "QPushButton{background:" + self._c
            + ";border:2px solid rgba(255,255,255,.15);border-radius:18px}"
            "QPushButton:hover{border:2px solid rgba(255,255,255,.5)}"
        )

    def _pick(self):
        c = QColorDialog.getColor(QColor(self._c), self)
        if c.isValid():
            self._c = c.name()
            self._rfr()
            self.colorChanged.emit(self._c)

    def setColor(self, c):
        self._c = c
        self._rfr()
        self.colorChanged.emit(c)


# ============================================================
#  Settings
# ============================================================
class SettingsWindow(QMainWindow):
    def __init__(self, cfg, presets, on_save):
        super().__init__()
        self.cfg = cfg
        self.presets = presets
        self._on_save = on_save
        self._tl = []
        self.setWindowTitle(T("title"))
        self.setFixedSize(460, 860)
        self.setWindowFlags(
            Qt.WindowType.Window | Qt.WindowType.WindowStaysOnTopHint
        )
        self._build()
        self._qss()

    def _at(self, w, k):
        self._tl.append((w, k))

    def _upd_lang(self):
        for w, k in self._tl:
            w.setText(T(k))
        self.setWindowTitle(T("title"))
        self._ref_mode()
        self._ref_click()

    def _ref_mode(self):
        self._mode.clear()
        self._mode.addItems([T("m0"), T("m1"), T("m2"), T("m3")])

    def _ref_click(self):
        self._click.clear()
        self._click.addItems([T("c0"), T("c1"), T("c2"), T("c3")])

    def _build(self):
        root = QWidget()
        self.setCentralWidget(root)
        lay = QVBoxLayout(root)
        lay.setContentsMargins(28, 20, 28, 16)
        lay.setSpacing(10)

        t = QLabel(T("title"))
        t.setObjectName("title")
        lay.addWidget(t)
        self._at(t, "title")
        s = QLabel(T("subtitle"))
        s.setObjectName("subtitle")
        lay.addWidget(s)
        self._at(s, "subtitle")
        lay.addWidget(self._sep())

        # language
        lr = QHBoxLayout()
        ll = QLabel(T("lang"))
        ll.setObjectName("fieldLabel")
        self._at(ll, "lang")
        lr.addWidget(ll)
        lr.addStretch()
        self._lcombo = QComboBox()
        self._lcombo.addItems(["中文", "English"])
        self._lcombo.setCurrentIndex(0 if _lang[0] == "zh" else 1)
        self._lcombo.currentIndexChanged.connect(self._swlang)
        self._lcombo.setFixedWidth(100)
        lr.addWidget(self._lcombo)
        lay.addLayout(lr)
        lay.addWidget(self._sep())

        # enable
        er = QHBoxLayout()
        el = QLabel(T("enable"))
        el.setObjectName("fieldLabel")
        self._at(el, "enable")
        self._chk = QCheckBox()
        self._chk.setChecked(self.cfg.get("enabled", True))
        self._chk.stateChanged.connect(self._toggled)
        er.addWidget(el)
        er.addStretch()
        er.addWidget(self._chk)
        lay.addLayout(er)
        lay.addWidget(self._sep())

        # trail mode
        ml = QLabel(T("trail_mode"))
        ml.setObjectName("fieldLabel")
        self._at(ml, "trail_mode")
        lay.addWidget(ml)
        self._mode = QComboBox()
        self._ref_mode()
        self._mode.setCurrentIndex(MIDX.get(self.cfg.get("mode", "glow"), 2))
        self._mode.currentIndexChanged.connect(self._mode_chg)
        lay.addWidget(self._mode)
        md = QLabel(T("mode_desc"))
        md.setObjectName("desc")
        md.setWordWrap(True)
        self._at(md, "mode_desc")
        lay.addWidget(md)
        lay.addWidget(self._sep())

        # click effect
        cl = QLabel(T("click_effect"))
        cl.setObjectName("fieldLabel")
        self._at(cl, "click_effect")
        lay.addWidget(cl)
        self._click = QComboBox()
        self._ref_click()
        self._click.setCurrentIndex(
            CIDX.get(self.cfg.get("click_effect", "ripple"), 1)
        )
        self._click.currentIndexChanged.connect(self._click_chg)
        lay.addWidget(self._click)
        cd = QLabel(T("click_desc"))
        cd.setObjectName("desc")
        self._at(cd, "click_desc")
        lay.addWidget(cd)
        lay.addWidget(self._sep())

        # color
        cl2 = QLabel(T("color"))
        cl2.setObjectName("fieldLabel")
        self._at(cl2, "color")
        lay.addWidget(cl2)
        crow = QHBoxLayout()
        crow.setSpacing(8)
        self._cbtn = CBtn(self.cfg.get("color", "#00ff88"))
        self._cbtn.colorChanged.connect(self._color_chg)
        crow.addWidget(self._cbtn)
        for pc in _COLORS:
            b = QPushButton()
            b.setFixedSize(24, 24)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            st = "QPushButton{background:" + pc
            st += ";border:2px solid transparent;border-radius:12px}"
            st += "QPushButton:hover{border:2px solid #fff}"
            b.setStyleSheet(st)
            b.clicked.connect(lambda _, c=pc: self._cbtn.setColor(c))
            crow.addWidget(b)
        crow.addStretch()
        lay.addLayout(crow)
        lay.addWidget(self._sep())

        # sliders
        self._ws = MSlider(T("width"), 1, 30, self.cfg.get("width", 8), "px")
        self._at(self._ws.lbl, "width")
        self._ws.valChanged.connect(self._w_chg)
        lay.addWidget(self._ws)

        dl = int(self.cfg.get("lifetime", 1.0) * 100)
        self._ls = MSlider(T("duration"), 10, 300, dl, "s", 0.01)
        self._at(self._ls.lbl, "duration")
        self._ls.valChanged.connect(self._l_chg)
        lay.addWidget(self._ls)

        self._ss = MSlider(T("sparkles"), 1, 10, self.cfg.get("sparkle_n", 3))
        self._at(self._ss.lbl, "sparkles")
        self._ss.valChanged.connect(self._s_chg)
        lay.addWidget(self._ss)
        lay.addWidget(self._sep())

        # presets
        pl = QLabel(T("preset_mgr"))
        pl.setObjectName("fieldLabel")
        self._at(pl, "preset_mgr")
        lay.addWidget(pl)

        pr = QHBoxLayout()
        pr.setSpacing(6)
        self._pname = QLineEdit()
        self._pname.setPlaceholderText(T("preset_name"))
        pr.addWidget(self._pname, 1)

        bsave = QPushButton(T("save"))
        self._at(bsave, "save")
        bsave.clicked.connect(self._p_save)
        pr.addWidget(bsave)

        bload = QPushButton(T("load"))
        self._at(bload, "load")
        bload.clicked.connect(self._p_load)
        pr.addWidget(bload)

        bdel = QPushButton(T("delete"))
        self._at(bdel, "delete")
        bdel.clicked.connect(self._p_del)
        pr.addWidget(bdel)
        lay.addLayout(pr)

        self._plist = QComboBox()
        self._plist.addItems(list(self.presets.keys()))
        lay.addWidget(self._plist)

        ior = QHBoxLayout()
        ior.setSpacing(10)
        bimp = QPushButton(T("import_f"))
        self._at(bimp, "import_f")
        bimp.clicked.connect(self._imp)
        ior.addWidget(bimp)
        bexp = QPushButton(T("export_f"))
        self._at(bexp, "export_f")
        bexp.clicked.connect(self._exp)
        ior.addWidget(bexp)
        lay.addLayout(ior)
        lay.addWidget(self._sep())

        # bottom
        br = QHBoxLayout()
        br.setSpacing(10)
        bres = QPushButton(T("reset"))
        self._at(bres, "reset")
        bres.clicked.connect(self._reset)
        bmin = QPushButton(T("minimize"))
        self._at(bmin, "minimize")
        bmin.clicked.connect(self.hide)
        br.addWidget(bres)
        br.addWidget(bmin)
        lay.addLayout(br)

        lay.addStretch()
        tip = QLabel(T("tip"))
        tip.setObjectName("tip")
        tip.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._at(tip, "tip")
        lay.addWidget(tip)

    def _sep(self):
        f = QFrame()
        f.setFrameShape(QFrame.Shape.HLine)
        f.setObjectName("sep")
        return f

    def refresh_plist(self):
        self._plist.clear()
        self._plist.addItems(list(self.presets.keys()))

    def _swlang(self, idx):
        _lang[0] = "en" if idx == 1 else "zh"
        self._upd_lang()
        self._on_save()

    def _toggled(self, state):
        self.cfg["enabled"] = (state == Qt.CheckState.Checked.value)

    def _mode_chg(self, i):
        self.cfg["mode"] = MKEY.get(i, "glow")

    def _click_chg(self, i):
        self.cfg["click_effect"] = CKEY.get(i, "none")

    def _color_chg(self, c):
        self.cfg["color"] = c

    def _w_chg(self, v):
        self.cfg["width"] = v

    def _l_chg(self, v):
        self.cfg["lifetime"] = v / 100.0

    def _s_chg(self, v):
        self.cfg["sparkle_n"] = v

    def _reset(self):
        self.cfg.update(DEFAULTS.copy())
        self.sync_ui()

    def sync_ui(self):
        self._chk.setChecked(self.cfg.get("enabled", True))
        self._mode.setCurrentIndex(MIDX.get(self.cfg.get("mode", "glow"), 2))
        self._click.setCurrentIndex(
            CIDX.get(self.cfg.get("click_effect", "ripple"), 1)
        )
        self._cbtn.setColor(self.cfg.get("color", "#00ff88"))
        self._ws.setVal(self.cfg.get("width", 8))
        self._ls.setVal(int(self.cfg.get("lifetime", 1.0) * 100))
        self._ss.setVal(self.cfg.get("sparkle_n", 3))

    def _p_save(self):
        name = self._pname.text().strip()
        if not name:
            QMessageBox.warning(self, "", T("err_name"))
            return
        if name in self.presets:
            r = QMessageBox.question(
                self, "", T("ow"),
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            )
            if r != QMessageBox.StandardButton.Yes:
                return
        self.presets[name] = {k: self.cfg.get(k) for k in _KEYS}
        self.refresh_plist()
        self._plist.setCurrentText(name)
        self._on_save()
        QMessageBox.information(self, "", T("saved"))

    def _p_load(self):
        name = self._plist.currentText()
        if name not in self.presets:
            return
        for k in _KEYS:
            if k in self.presets[name]:
                self.cfg[k] = self.presets[name][k]
        self.sync_ui()
        self._on_save()
        QMessageBox.information(self, "", T("loaded"))

    def _p_del(self):
        name = self._plist.currentText()
        if name not in self.presets:
            return
        r = QMessageBox.question(
            self, "", T("del_confirm"),
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
        )
        if r != QMessageBox.StandardButton.Yes:
            return
        del self.presets[name]
        self.refresh_plist()
        self._on_save()
        QMessageBox.information(self, "", T("deleted"))

    def _imp(self):
        path, _ = QFileDialog.getOpenFileName(self, "", "", "JSON (*.json)")
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if "presets" in data:
                self.presets.update(data["presets"])
            elif "settings" in data:
                n = os.path.basename(path).replace(".json", "")
                self.presets[n] = data["settings"]
            self.refresh_plist()
            self._on_save()
            QMessageBox.information(self, "", T("import_ok"))
        except Exception as e:
            QMessageBox.warning(self, "", str(e))

    def _exp(self):
        name = self._plist.currentText()
        if name not in self.presets:
            return
        path, _ = QFileDialog.getSaveFileName(
            self, "", name + ".json", "JSON (*.json)"
        )
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(
                    {"name": name, "settings": self.presets[name]},
                    f, ensure_ascii=False, indent=2,
                )
            QMessageBox.information(self, "", T("export_ok"))
        except Exception as e:
            QMessageBox.warning(self, "", str(e))

    def closeEvent(self, e):
        e.ignore()
        self.hide()

    def _qss(self):
        q = [
            "QMainWindow, QWidget { background: #0c0c1d; }",
            "#title { font-size: 20px; font-weight: 700; color: #f0f0f0; border: none; background: none; }",
            "#subtitle { font-size: 12px; color: #555; border: none; background: none; }",
            "#fieldLabel { font-size: 12px; color: #777; font-weight: 600; border: none; background: none; }",
            "#desc { font-size: 11px; color: #444; border: none; background: none; }",
            "#tip { font-size: 10px; color: #333; border: none; background: none; }",
            "QFrame#sep { color: #1a1a30; border: none; background: none; max-height: 1px; }",
            "QPushButton { background: #161630; color: #999; border: 1px solid #252545; border-radius: 8px; padding: 10px 18px; font-size: 13px; }",
            "QPushButton:hover { background: #1e1e3c; border-color: #4a4a80; color: #fff; }",
            "QPushButton:pressed { background: #0e0e22; }",
            "QComboBox { background: #141430; color: #ddd; border: 1px solid #252545; border-radius: 8px; padding: 8px 14px; font-size: 13px; }",
            "QComboBox:hover { border-color: #4a4a80; }",
            "QComboBox::drop-down { border: none; width: 28px; }",
            "QComboBox QAbstractItemView { background: #141430; color: #ddd; border: 1px solid #252545; selection-background-color: #0f3460; border-radius: 6px; padding: 4px; }",
            "QCheckBox { spacing: 8px; }",
            "QCheckBox::indicator { width: 42px; height: 22px; border-radius: 11px; background: #252545; }",
            "QCheckBox::indicator:checked { background: #00ff88; }",
            "QCheckBox::indicator:hover { background: #3a3a5c; }",
            "QSlider::groove:horizontal { height: 4px; background: #252545; border-radius: 2px; }",
            "QSlider::handle:horizontal { background: #00ff88; width: 16px; height: 16px; margin: -6px 0; border-radius: 8px; }",
            "QSlider::handle:horizontal:hover { background: #33ffaa; }",
            "QSlider::sub-page:horizontal { background: #00cc6a; border-radius: 2px; }",
            "QLineEdit { background: #141430; color: #ddd; border: 1px solid #252545; border-radius: 8px; padding: 8px 12px; font-size: 13px; }",
            "QLineEdit:focus { border-color: #00ff88; }",
            "QLabel { color: #999; font-size: 13px; border: none; background: none; }",
        ]
        self.setStyleSheet("\n".join(q))


# ============================================================
#  App
# ============================================================
class App:
    def __init__(self):
        self.qapp = QApplication(sys.argv)
        self.qapp.setQuitOnLastWindowClosed(False)

        data = load_file()
        if data:
            self.cfg = data.get("settings", DEFAULTS.copy())
            self.presets = data.get("presets", {})
            _lang[0] = data.get("language", "zh")
        else:
            self.cfg = DEFAULTS.copy()
            self.presets = {}

        self.overlay = Overlay(self.cfg)
        self.overlay.show()

        self.settings = SettingsWindow(self.cfg, self.presets, self._do_save)
        self._setup_tray()
        self.qapp.aboutToQuit.connect(self._cleanup)
        self._exiting = False

    def _do_save(self):
        save_file(self.cfg, self.presets, _lang[0])

    def _setup_tray(self):
        pm = QPixmap(64, 64)
        pm.fill(QColor(0, 0, 0, 0))
        p = QPainter(pm)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor("#00ff88"))
        p.drawEllipse(4, 4, 56, 56)
        p.setBrush(QColor("#0c0c1d"))
        p.drawEllipse(12, 12, 40, 40)
        p.setBrush(QColor("#ffffff"))
        p.drawEllipse(24, 24, 16, 16)
        p.end()

        self.tray = QSystemTrayIcon(QIcon(pm), self.qapp)
        menu = QMenu()
        ms = "QMenu{background:#141430;color:#ddd;border:1px solid #252545;border-radius:6px;padding:4px}"
        ms += "QMenu::item{padding:8px 28px;border-radius:4px}"
        ms += "QMenu::item:selected{background:#0f3460}"
        ms += "QMenu::separator{height:1px;background:#252545;margin:4px 8px}"
        menu.setStyleSheet(ms)

        self._ta = QAction(T("pause"), self.qapp)
        self._ta.triggered.connect(self._toggle)
        menu.addAction(self._ta)

        sa = QAction(T("open_set"), self.qapp)
        sa.triggered.connect(self._show)
        menu.addAction(sa)

        menu.addSeparator()

        qa = QAction(T("exit"), self.qapp)
        qa.triggered.connect(self._quit)
        menu.addAction(qa)

        self.tray.setContextMenu(menu)
        self.tray.activated.connect(self._activated)
        self.tray.setToolTip(T("tray_run"))
        self.tray.show()

    def _toggle(self):
        self.cfg["enabled"] = not self.cfg["enabled"]
        if self.cfg["enabled"]:
            self.overlay.show()
            self._ta.setText(T("pause"))
            self.tray.setToolTip(T("tray_run"))
        else:
            self.overlay.hide()
            self._ta.setText(T("resume"))
            self.tray.setToolTip(T("tray_pause"))
        self.settings.sync_ui()

    def _show(self):
        self.settings.sync_ui()
        self.settings.show()
        self.settings.raise_()
        self.settings.activateWindow()

    def _activated(self, reason):
        if reason == QSystemTrayIcon.ActivationReason.DoubleClick:
            self._show()

    def _quit(self):
        if self._exiting:
            return
        self._exiting = True
        self._cleanup()
        self.qapp.quit()

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
        self._do_save()

    def run(self):
        return self.qapp.exec()


if __name__ == "__main__":
    app = App()
    sys.exit(app.run())
