import copy
import customtkinter as ctk
import json
import os
import queue
import re
import ctypes
import threading
import time
from datetime import datetime

try:
    import winsound
    _HAS_WINSOUND = True
except ImportError:
    _HAS_WINSOUND = False

SCRIPT_DIR   = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE  = os.path.join(SCRIPT_DIR, "timer_config.json")
SESSION_FILE = os.path.join(SCRIPT_DIR, "timer_session.json")

# ── Serialised beep worker — one thread, no overlapping Beep() calls ──────────
# #10: only start the thread when winsound is actually available
_beep_queue = queue.Queue()

def _beep_worker():
    while True:
        freq, dur = _beep_queue.get()
        try:
            winsound.Beep(freq, dur)
        except Exception:
            pass
        _beep_queue.task_done()

if _HAS_WINSOUND:
    threading.Thread(target=_beep_worker, daemon=True).start()


def _make_timer():
    return {
        'remaining':          0,
        'running':            False,
        'paused':             False,
        'done':               False,
        'loop':               False,
        'duration':           0,
        'chain_to':           None,
        'waiting_for_chain':  False,
        'start_wall':         0.0,
        'remaining_at_start': 0,
    }


def _live_remaining(t):
    """Current remaining seconds for a timer, accounting for wall-clock elapsed if running."""
    if t['running']:
        return max(0, t['remaining_at_start'] - int(time.time() - t['start_wall']))
    return t['remaining']


# ── #9: module-level pure functions (no self) ──────────────────────────────────

def _deep_merge(base, override):
    # #2: fixed docstring — override wins for all present keys, base fills gaps
    """Merge override into base; override values win, base fills missing keys."""
    result = base.copy()
    for k, v in override.items():
        if k in result and isinstance(result[k], dict) and isinstance(v, dict):
            result[k] = _deep_merge(result[k], v)
        elif isinstance(v, list):
            result[k] = v[:]   # shallow copy — prevents merged config sharing list with caller
        else:
            result[k] = v
    return result


def _fmt_seconds(n):
    """Return compact H:MM:SS or MM:SS string."""
    n = max(0, int(n))
    h, r = divmod(n, 3600)
    m, s = divmod(r, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"


def _fmt_label(n):
    """Return compact label like 1h30m, 5m, 45s for saving presets/groups."""
    n = max(0, int(n))
    h, r = divmod(n, 3600)
    m, s = divmod(r, 60)
    if h and m and s: return f"{h}h{m}m{s}s"
    if h and m:   return f"{h}h{m}m"
    if h:         return f"{h}h"
    if m and s:   return f"{m}m{s}s"
    if m:         return f"{m}m"
    return f"{s}s"


class TimerApp:
    def __init__(self):
        self.root = ctk.CTk()
        self.root.title("Timer")
        self.root.attributes('-topmost', True)
        self.root.overrideredirect(True)
        self.root.configure(fg_color="#2a2a2a")

        self.config_file  = CONFIG_FILE
        self.session_file = SESSION_FILE
        self.load_config()

        self.timers         = [_make_timer() for _ in range(5)]
        self.visible_timers = 2
        self.active_group   = None
        self._flashing      = [False] * 5

        # Volume
        self.volume_dragging        = False
        self.volume_start_x         = 0
        self.volume_start_vol       = 0
        self.last_set_volume        = None
        self.manual_volume_control  = False
        self._volume_interface      = None
        self._volume_unavailable    = False
        self._volume_toast_alive    = False   # #3: boolean guard, same pattern as ldrag toast
        self._is_headphones         = None    # None=unknown, True=headphones, False=speakers

        # Toast
        self._toast_window   = None
        self._toast_label    = None
        self._toast_after_id = None
        self._toast_queue    = []
        self.volume_toast    = None

        # Window drag
        self.drag_start_x = 0
        self.drag_start_y = 0
        self.drag_x       = 0
        self.drag_y       = 0
        self.drag_moved   = False
        self.click_time   = 0.0
        self._menu_open   = False   # #4: singleton guard for context menu

        self.is_collapsed    = False
        self._session_dirty  = False
        self._autosave_fail_count = 0
        self._drag_click_id  = None   # debounce for datetime-handle single-click → menu
        self._last_cleared  = [None] * 5

        # Per-timer click debounce
        self._timer_click_ids = [None] * 5

        # Per-timer left-drag scrub state
        self._ldrag_start_x     = [0]     * 5
        self._ldrag_start_rem   = [0]     * 5
        self._ldrag_moved       = [False] * 5
        self._ldrag_toast       = None
        self._ldrag_toast_alive = False

        # Scroll-toast debounce (one pending after-id per timer slot)
        self._scroll_toast_ids = [None] * 5

        self.build_ui()

        if 'window_x' in self.config and 'window_y' in self.config:
            self.root.geometry(f"+{self.config['window_x']}+{self.config['window_y']}")

        self.restore_session()
        self.update_timers()
        self.update_clock()
        self.update_volume_display()
        self.autosave_session()

    # ─────────────────────────────────────────────
    # Config
    # ─────────────────────────────────────────────

    def load_config(self):
        defaults = {
            "_help": {
                "presets":         "Timer durations in seconds. Labels show in dropdowns.",
                "groups":          "Timer indices 0-4. chain_to starts another timer on finish.",
                "sounds":          "Beep Hz per timer. Edit here or via 'Sounds' in menu.",
                "saved_positions": "Saved window positions (managed by app).",
            },
            "presets": {
                "durations_seconds": [30, 60, 120, 180, 300, 420, 600, 900, 1200, 1800, 3600],
                "labels":            ["30s","1m","2m","3m","5m","7m","10m","15m","20m","30m","1h"]
            },
            "groups": {
                "Pomodoro": [
                    {"time": "25m", "loop": False, "chain_to": 1},
                    {"time": "5m",  "loop": False, "chain_to": 0}
                ],
                "Tea":     ["3m"],
                "Cooking": ["10m", "15m"]
            },
            "sounds": {
                "timer1_hz": 750, "timer2_hz": 850, "timer3_hz": 650,
                "timer4_hz": 950, "timer5_hz": 550
            },
            "saved_positions": {}
        }

        if os.path.exists(self.config_file):
            try:
                with open(self.config_file, 'r') as f:
                    loaded = json.load(f)
                if 'preset_labels' in loaded:
                    self.config = self._migrate_old_config(loaded, defaults)
                else:
                    # For collections the user can delete (groups, presets), the loaded
                    # file must win entirely — don't let defaults re-inject deleted entries.
                    merge_base = copy.deepcopy(defaults)
                    if 'groups'  in loaded: merge_base.pop('groups',  None)
                    if 'presets' in loaded: merge_base.pop('presets', None)
                    self.config = _deep_merge(merge_base, loaded)
            except Exception:
                self.config = copy.deepcopy(defaults)
        else:
            self.config = copy.deepcopy(defaults)
            self.save_config()

        p = self.config.get('presets', {})
        self.preset_values = list(p.get('durations_seconds', defaults['presets']['durations_seconds']))
        self.preset_labels  = list(p.get('labels',            defaults['presets']['labels']))
        # Guard against hand-edited config with mismatched list lengths
        _n = min(len(self.preset_labels), len(self.preset_values))
        self.preset_labels  = self.preset_labels[:_n]
        self.preset_values  = self.preset_values[:_n]
        # Sort by duration so the list is always in order regardless of how it was saved
        if self.preset_values:
            _sorted = sorted(zip(self.preset_values, self.preset_labels))
            self.preset_values, self.preset_labels = [list(x) for x in zip(*_sorted)]

        s = self.config.get('sounds', {})
        self.sound_freqs = [
            s.get('timer1_hz', 750), s.get('timer2_hz', 850), s.get('timer3_hz', 650),
            s.get('timer4_hz', 950), s.get('timer5_hz', 550),
        ]

    def _migrate_old_config(self, old, defaults):
        new = copy.deepcopy(defaults)
        new['presets'] = {
            'durations_seconds': list(old.get('presets',       defaults['presets']['durations_seconds'])),
            'labels':            list(old.get('preset_labels', defaults['presets']['labels']))
        }
        old_groups, new_groups = old.get('groups', {}), {}
        for name, timers in old_groups.items():
            new_groups[name] = []
            for t in timers:
                if isinstance(t, dict):
                    entry = t.copy(); entry.setdefault('chain_to', None)
                    new_groups[name].append(entry)
                else:
                    new_groups[name].append({"time": t, "loop": False, "chain_to": None})
        new['groups'] = new_groups
        if 'sounds' in old and isinstance(old['sounds'], list):
            keys = ['timer1_hz','timer2_hz','timer3_hz','timer4_hz','timer5_hz']
            defs = [750, 850, 650, 950, 550]
            new['sounds'] = {k: old['sounds'][i] if i < len(old['sounds']) else defs[i]
                             for i, k in enumerate(keys)}
        elif 'sounds' in old and isinstance(old['sounds'], dict):
            # Already a dict — preserve user-customised Hz values (copy to avoid aliasing)
            new['sounds'] = dict(old['sounds'])
        new['saved_positions'] = old.get('saved_positions', {})
        return new

    def save_config(self):
        tmp = self.config_file + '.tmp'
        try:
            with open(tmp, 'w') as f:
                json.dump(self.config, f, indent=4)
            os.replace(tmp, self.config_file)
        except Exception:
            try: os.remove(tmp)
            except Exception: pass
            raise

    # ── #11: preset mutation always through these two helpers ─────────────────

    def _add_preset(self, label, seconds):
        """Add a preset in duration-sorted order, keeping labels and values in sync."""
        import bisect
        idx = bisect.bisect_left(self.preset_values, seconds)
        self.preset_labels.insert(idx, label)
        self.preset_values.insert(idx, seconds)
        self.config['presets']['labels']            = self.preset_labels
        self.config['presets']['durations_seconds'] = self.preset_values

    def _remove_preset(self, idx):
        """Remove a preset by index, keeping labels and values in sync."""
        if 0 <= idx < len(self.preset_labels):
            self.preset_labels.pop(idx)
            self.preset_values.pop(idx)
            self.config['presets']['labels']            = self.preset_labels
            self.config['presets']['durations_seconds'] = self.preset_values

    def _reload_preset_dropdowns(self):
        items = ["", "+1m", "+5m", "-1m", "-5m", "---"] + self.preset_labels
        for tw in self.timer_widgets:
            try: tw['preset_menu'].configure(values=items)
            except Exception: pass

    # ── #12: shared popup factory ──────────────────────────────────────────────

    def _make_popup(self):
        """Create a topmost borderless popup. Returns (win, destroy_fn)."""
        win = ctk.CTkToplevel(self.root)
        win.attributes('-topmost', True)
        win.overrideredirect(True)
        _destroyed = [False]   # closure list so destroy() can mutate it
        def destroy():
            if not _destroyed[0]:
                _destroyed[0] = True
                try: win.destroy()
                except Exception: pass
        return win, destroy

    # ─────────────────────────────────────────────
    # Session
    # ─────────────────────────────────────────────

    def save_session(self):
        snapshot = {
            'saved_at':       time.time(),
            'visible_timers': self.visible_timers,
            'active_group':   self.active_group,
            'is_collapsed':   self.is_collapsed,
            'timers':         []
        }
        for t in self.timers:
            rem = _live_remaining(t)
            snapshot['timers'].append({
                'remaining':         rem,
                'running':           t['running'],
                'paused':            t['paused'],
                'done':              t['done'],
                'loop':              t['loop'],
                'duration':          t['duration'],
                'chain_to':          t['chain_to'],
                'waiting_for_chain': t['waiting_for_chain'],
            })
        tmp = self.session_file + '.tmp'
        try:
            with open(tmp, 'w') as f:
                json.dump(snapshot, f, indent=4)
            os.replace(tmp, self.session_file)
        except Exception:
            try: os.remove(tmp)
            except Exception: pass
            raise   # let autosave_session count failures and warn the user

    def restore_session(self):
        if not os.path.exists(self.session_file):
            return
        try:
            with open(self.session_file, 'r') as f:
                session = json.load(f)
        except Exception:
            return

        elapsed = max(0, min(int(time.time() - session.get('saved_at', 0)), 86400))
        self.set_visible_timers(session.get('visible_timers', 2))
        self.active_group = session.get('active_group')

        if session.get('is_collapsed', False):
            self.timer_row.pack_forget()
            self.is_collapsed = True

        any_remaining = False
        restored_any  = False

        for i, saved in enumerate(session.get('timers', [])[:5]):
            t = self.timers[i]
            t['duration']          = saved.get('duration', 0)
            t['loop']              = saved.get('loop', False)
            t['chain_to']          = saved.get('chain_to', None)
            t['waiting_for_chain'] = saved.get('waiting_for_chain', False)
            t['done']              = saved.get('done', False)

            if saved.get('running'):
                new_rem = saved.get('remaining', 0) - elapsed
                if new_rem > 0:
                    t['remaining'] = t['remaining_at_start'] = new_rem
                    t['start_wall'] = time.time()
                    t['running']    = True
                    t['paused']     = False
                    restored_any = any_remaining = True
                else:
                    # Timer expired while the app was closed — show done state
                    t['remaining'] = 0; t['running'] = False; t['paused'] = False
                    t['done'] = True
                    restored_any = True
            elif saved.get('paused'):
                t['remaining'] = saved.get('remaining', 0)
                t['running']   = False; t['paused'] = True
                restored_any   = True
                if t['remaining'] > 0: any_remaining = True
            elif saved.get('waiting_for_chain'):
                t['remaining'] = 0; t['running'] = False; t['paused'] = False
                restored_any   = True
                any_remaining  = True   # chain session is still live
            else:
                t['remaining'] = saved.get('remaining', 0)
                t['running']   = False; t['paused'] = False

            self.update_display(i)

        if not any_remaining:
            self.active_group = None
        if restored_any:
            hint = f" ({self.active_group})" if self.active_group else ""
            self.show_toast(f"Session restored{hint}")
        # Startup restore is not a user change — don't trigger an immediate autosave
        self._session_dirty = False

    def autosave_session(self):
        try:
            if self._session_dirty:
                self.save_session()
                self._session_dirty = False
                self._autosave_fail_count = 0
        except Exception:
            self._autosave_fail_count += 1
            if self._autosave_fail_count == 3:   # toast once after ~15s of repeated failures
                self.show_toast("Warning: session could not be saved")
        self.root.after(5000, self.autosave_session)

    # ─────────────────────────────────────────────
    # UI construction
    # ─────────────────────────────────────────────

    def build_ui(self):
        ctk.set_appearance_mode("dark")

        row = ctk.CTkFrame(self.root, fg_color="#2a2a2a")
        row.pack(padx=0, pady=0)

        self.datetime_handle = ctk.CTkLabel(
            row, text="Mon 01 12:34", font=("Arial", 13, "bold"),
            width=80, height=15, fg_color="#3a3a3a", corner_radius=0
        )
        self.datetime_handle.pack(side='left', padx=(0, 1))
        self.datetime_handle.bind('<Button-1>',        self.handle_drag_click)
        self.datetime_handle.bind('<B1-Motion>',       self.on_drag)
        self.datetime_handle.bind('<ButtonRelease-1>', self.handle_drag_release)
        self.datetime_handle.bind('<Double-Button-1>', self.on_double_click)

        self.drag_handle = ctk.CTkLabel(
            row, text="--", font=("Arial", 13, "bold"),
            width=44, height=18, fg_color="#cc7722", text_color="#000000", corner_radius=0
        )
        self.drag_handle.pack(side='left', padx=(0, 1))
        self.drag_handle.bind('<Button-1>',        self.start_volume_drag)
        self.drag_handle.bind('<B1-Motion>',       self.on_volume_drag)
        self.drag_handle.bind('<ButtonRelease-1>', self.end_volume_drag)

        self.timer_row = ctk.CTkFrame(row, fg_color="#2a2a2a")
        self.timer_row.pack(side='left')

        self.timer_widgets = []
        for i in range(5):
            tw = self.create_inline_timer(self.timer_row, i)
            self.timer_widgets.append(tw)
            if i >= 2:
                tw['frame'].pack_forget()

        self.root.update()

    def create_inline_timer(self, parent, index):
        frame = ctk.CTkFrame(parent, fg_color="#2a2a2a")
        frame.pack(side='left', padx=0)

        display = ctk.CTkLabel(
            frame, text="00:00",
            font=("Consolas", 15, "bold"),
            width=58, height=15,
            fg_color="#3a3a3a", text_color="#404040",
            corner_radius=0, cursor="hand2"
        )
        display.pack(side='left', padx=0)

        display.bind('<Button-1>',        lambda e, i=index: self._timer_press(i, e))
        display.bind('<B1-Motion>',       lambda e, i=index: self._timer_drag(i, e))
        display.bind('<ButtonRelease-1>', lambda e, i=index: self._timer_release(i, e))
        display.bind('<Double-Button-1>', lambda e, i=index: self._on_timer_double_click(i))
        display.bind('<Button-2>',        lambda e, i=index: self.clear_timer(i))
        display.bind('<Button-3>',        lambda e, i=index: self.toggle_loop(i))
        display.bind('<MouseWheel>',       lambda e, i=index: self._scroll_adjust(i, e.delta, fine=False))
        display.bind('<Shift-MouseWheel>', lambda e, i=index: self._scroll_adjust(i, e.delta, fine=True))
        display.bind('<Control-z>',        lambda e, i=index: self.undo_clear(i))

        preset_var     = ctk.StringVar(value="")
        dropdown_items = ["", "+1m", "+5m", "-1m", "-5m", "---"] + self.preset_labels
        preset_menu = ctk.CTkOptionMenu(
            frame, variable=preset_var, width=6, height=15,
            values=dropdown_items,
            command=lambda choice, i=index: self.handle_dropdown_choice(i, choice),
            fg_color="#2a2a2a", button_color="#2d2d2d",
            button_hover_color="#333333",
            font=("Arial", 5), corner_radius=0,
            dropdown_font=("Arial", 13, "bold"),
            dropdown_fg_color="#2a2a2a",
            dropdown_hover_color="#3a3a3a",
            anchor="center"
        )
        preset_menu.pack(side='left', padx=0, pady=0)

        return {'frame': frame, 'display': display, 'preset_var': preset_var, 'preset_menu': preset_menu}

    # ─────────────────────────────────────────────
    # Left-button: scrub drag + click/double-click
    # ─────────────────────────────────────────────

    def _timer_press(self, index, event):
        if self._timer_click_ids[index] is not None:
            self.root.after_cancel(self._timer_click_ids[index])
            self._timer_click_ids[index] = None
        t = self.timers[index]
        if t['running']:
            t['remaining'] = _live_remaining(t)
        self._ldrag_start_x[index]   = event.x_root
        self._ldrag_start_rem[index] = t['remaining']
        self._ldrag_moved[index]     = False

    def _timer_drag(self, index, event):
        delta_px = event.x_root - self._ldrag_start_x[index]
        if abs(delta_px) < 5:
            return

        # Cancel any pending scroll toast so it doesn't overlap the drag toast
        if self._scroll_toast_ids[index] is not None:
            self.root.after_cancel(self._scroll_toast_ids[index])
            self._scroll_toast_ids[index] = None

        self._ldrag_moved[index] = True
        t    = self.timers[index]
        base = self._ldrag_start_rem[index]

        if base <= 0:       px_per_sec = 1.0
        elif base <= 300:   px_per_sec = 2.0
        elif base <= 1800:  px_per_sec = 0.5
        elif base <= 7200:  px_per_sec = 0.15
        else:               px_per_sec = 0.05

        new_rem = max(0, base + int(delta_px / px_per_sec))

        t['remaining']          = new_rem
        t['remaining_at_start'] = new_rem
        t['start_wall']         = time.time()
        if new_rem > 0:
            t['duration'] = new_rem
            t['waiting_for_chain'] = False   # drag overrides chain-wait
            if not t['running'] and not t['paused']:
                t['running'] = True
        else:
            # Dragged to zero — stop completely regardless of paused state
            # (waiting_for_chain is only cleared when a positive value is set, above)
            t['running'] = False; t['paused'] = False
        t['done'] = False
        self._session_dirty = True
        self.update_display(index)
        self._show_ldrag_toast(index, new_rem)

    def _timer_release(self, index, event):
        if self._ldrag_moved[index]:
            self._hide_ldrag_toast()
            self._ldrag_moved[index] = False
        else:
            self._timer_click_ids[index] = self.root.after(
                220, lambda: self._on_timer_single_click(index)
            )

    def _on_timer_single_click(self, index):
        self._timer_click_ids[index] = None
        t = self.timers[index]
        if t['done']:
            # First click on a finished timer just dismisses the alarm glow
            t['done'] = False
            self._session_dirty = True
            self.update_display(index)
            return
        if t['running'] or t['paused']:
            self.toggle_pause(index)
        elif not t['waiting_for_chain']:
            self.open_duration_entry(index)

    def _on_timer_double_click(self, index):
        if self._timer_click_ids[index] is not None:
            self.root.after_cancel(self._timer_click_ids[index])
            self._timer_click_ids[index] = None
        self._ldrag_moved[index] = False
        self.timers[index]['done'] = False
        self.restart_timer(index)

    # ─────────────────────────────────────────────
    # Left-drag scrub toast
    # ─────────────────────────────────────────────

    def _show_ldrag_toast(self, index, remaining):
        text = f"T{index+1}: {_fmt_seconds(remaining)}"

        if self._ldrag_toast_alive:
            try:
                self._ldrag_toast_label.configure(text=text)
            except Exception:
                pass
            return

        self._ldrag_toast_alive = True
        self._ldrag_toast = ctk.CTkToplevel(self.root)
        self._ldrag_toast.attributes('-topmost', True)
        self._ldrag_toast.overrideredirect(True)
        frame = ctk.CTkFrame(self._ldrag_toast, fg_color="#2a2a2a")
        frame.pack(padx=2, pady=2)
        self._ldrag_toast_label = ctk.CTkLabel(frame, text=text, font=("Arial", 9))
        self._ldrag_toast_label.pack(padx=10, pady=5)
        x = self.root.winfo_x()
        y = self.root.winfo_y() - 40
        if y < 0:
            y = self.root.winfo_y() + self.root.winfo_height() + 5
        self._ldrag_toast.geometry(f"+{x}+{y}")

    def _hide_ldrag_toast(self):
        self._ldrag_toast_alive = False
        try:
            if self._ldrag_toast is not None:
                self._ldrag_toast.destroy()
        except Exception:
            pass
        self._ldrag_toast = None

    # ─────────────────────────────────────────────
    # Duration entry popup
    # ─────────────────────────────────────────────

    def open_duration_entry(self, index):
        win, destroy = self._make_popup()   # #12

        frame = ctk.CTkFrame(win, fg_color="#3a3a3a", corner_radius=4)
        frame.pack(padx=2, pady=2)
        ctk.CTkLabel(frame, text=f"T{index+1}:", font=("Arial", 9),
                     text_color="#aaaaaa").pack(side='left', padx=(6, 2), pady=4)
        entry_var = ctk.StringVar()
        entry = ctk.CTkEntry(frame, textvariable=entry_var, width=70, height=18,
                             font=("Consolas", 12), fg_color="#2a2a2a", border_width=0,
                             corner_radius=2, placeholder_text="5m, 1h30m, 90...")  # #13: updated hint
        entry.pack(side='left', padx=(0, 6), pady=4)

        def commit(event=None):
            secs = self.parse_duration(entry_var.get().strip())
            if secs and secs > 0:
                self.start_timer(index, secs); destroy()
            else:
                self.show_toast("Invalid duration")
                try: entry.select_range(0, 'end'); entry.focus_force()
                except Exception: pass

        entry.bind('<Return>',   commit)
        entry.bind('<KP_Enter>', commit)
        entry.bind('<Escape>',   lambda e: destroy())

        def _focus_out(e):
            try:    fw = win.focus_get()
            except: fw = None
            if fw is None: destroy()

        win.bind('<FocusOut>', _focus_out)

        widget = self.timer_widgets[index]['display']
        wx = widget.winfo_rootx()
        wy = widget.winfo_rooty() + widget.winfo_height() + 4
        self.root.update_idletasks(); win.update_idletasks()
        sw = self.root.winfo_screenwidth(); sh = self.root.winfo_screenheight()
        ph = win.winfo_reqheight()
        wx = min(wx, sw - win.winfo_reqwidth() - 4)
        if wy + ph > sh: wy = widget.winfo_rooty() - ph - 4
        win.geometry(f"+{wx}+{wy}")
        try: entry.focus_force()
        except Exception: pass

    # ─────────────────────────────────────────────
    # Timer logic
    # ─────────────────────────────────────────────

    def handle_dropdown_choice(self, index, choice):
        if choice in ("", "---"):
            self.root.after(100, lambda: self.timer_widgets[index]['preset_var'].set(""))
            return
        if choice in ("+1m", "+5m", "-1m", "-5m"):
            deltas = {"+1m": 60, "+5m": 300, "-1m": -60, "-5m": -300}
            self.adjust_timer(index, deltas[choice])
        else:
            try:
                i = self.preset_labels.index(choice)
                self.start_timer(index, self.preset_values[i])
                self.show_toast(f"T{index+1}: {choice}")   # #14: toast on preset load
            except (ValueError, IndexError):
                pass
        self.root.after(100, lambda: self.timer_widgets[index]['preset_var'].set(""))

    def toggle_loop(self, index):
        t = self.timers[index]
        t['loop'] = not t['loop']
        self._session_dirty = True
        self.update_display(index)
        self.show_toast(f"T{index+1} loop: {'ON' if t['loop'] else 'OFF'}")

    def start_timer(self, index, seconds):
        t = self.timers[index]
        t['duration']           = seconds
        t['remaining']          = seconds
        t['remaining_at_start'] = seconds
        t['start_wall']         = time.time()
        t['running']            = True
        t['paused']             = False
        t['waiting_for_chain']  = False
        t['done']               = False
        self._session_dirty     = True
        self.update_display(index)

    def clear_timer(self, index):
        t = self.timers[index]
        if t['duration'] > 0 or t['remaining'] > 0:
            self._last_cleared[index] = {k: v for k, v in t.items()}
        # Preserve chain_to and loop — they're invisible config the user set intentionally.
        # Only reset the timing/state fields.
        t.update({'remaining': 0, 'remaining_at_start': 0, 'start_wall': 0.0,
                  'duration': 0, 'running': False, 'paused': False,
                  'waiting_for_chain': False, 'done': False})
        self._session_dirty = True
        try: self.save_session()
        except Exception: pass
        self.update_display(index)

    def restart_timer(self, index):
        t = self.timers[index]
        if t['duration'] > 0:
            self.start_timer(index, t['duration'])

    def undo_clear(self, index):
        snapshot = self._last_cleared[index]
        if snapshot is None:
            self.show_toast(f"Nothing to undo for T{index+1}"); return
        t = self.timers[index]
        for k, v in snapshot.items(): t[k] = v
        if t['running']:
            t['remaining_at_start'] = t['remaining']; t['start_wall'] = time.time()
        self._last_cleared[index] = None
        self._session_dirty = True
        self.update_display(index)
        self.show_toast(f"T{index+1} restored")

    def adjust_timer(self, index, seconds, silent=False):
        t = self.timers[index]
        if t['running']:
            t['remaining'] = _live_remaining(t)
        new_time = max(0, t['remaining'] + seconds)

        if new_time > 0:
            t['remaining'] = t['remaining_at_start'] = new_time
            t['start_wall'] = time.time()
            t['waiting_for_chain'] = False   # scroll/dropdown overrides chain-wait, same as drag
            if not t['running'] and not t['paused']:
                t['running'] = True
            t['duration'] = new_time   # always update so double-click restart reflects adjusted value
        else:
            t['remaining'] = t['remaining_at_start'] = 0
            t['running'] = t['paused'] = False
        t['done'] = False
        self._session_dirty = True
        self.update_display(index)

        if not silent:
            self.show_toast(f"T{index+1} -> {_fmt_seconds(t['remaining'])}")

    def toggle_pause(self, index):
        t = self.timers[index]
        live = _live_remaining(t)
        if live > 0:
            if t['running']:
                t['remaining'] = live
                t['running'] = False; t['paused'] = True
            elif t['paused']:
                t['remaining_at_start'] = t['remaining']
                t['start_wall']         = time.time()
                t['running'] = True; t['paused'] = False
            self._session_dirty = True
            self.update_display(index)

    # ─────────────────────────────────────────────
    # Scroll: adaptive + fine; works on idle
    # ─────────────────────────────────────────────

    def _adaptive_step(self, remaining):
        if remaining <= 300:    return 15
        elif remaining <= 1800: return 60
        elif remaining <= 7200: return 300
        else:                   return 900

    def _scroll_adjust(self, index, delta, fine=False):
        rem = self.timers[index]['remaining']
        base_step = self._adaptive_step(rem) if rem > 0 else 60
        step = max(5, base_step // 4) if fine else base_step
        self.adjust_timer(index, step if delta > 0 else -step, silent=True)
        if self._scroll_toast_ids[index] is not None:
            self.root.after_cancel(self._scroll_toast_ids[index])
        t = self.timers[index]
        self._scroll_toast_ids[index] = self.root.after(
            300, lambda rem=t['remaining']: self._emit_scroll_toast(index, rem)
        )

    def _emit_scroll_toast(self, index, remaining):
        self._scroll_toast_ids[index] = None
        self.show_toast(f"T{index+1} -> {_fmt_seconds(remaining)}")

    # ─────────────────────────────────────────────
    # Display / tick
    # ─────────────────────────────────────────────

    def update_display(self, index):
        t      = self.timers[index]
        widget = self.timer_widgets[index]

        # Read current remaining without mutating — state writes belong in tick/logic methods
        remaining = _live_remaining(t)

        base = _fmt_seconds(remaining)
        loop_pfx   = "~" if t['loop'] else ""
        chain_sfx  = ">" if t['chain_to'] is not None else ""   # visible chain indicator

        if t['waiting_for_chain']:
            text = "|-:--"; fg = "#5588cc"
        elif t['running']:
            text = loop_pfx + base + chain_sfx; fg = "#00cc00"
        elif t['paused']:
            text = loop_pfx + base + chain_sfx; fg = "#cc8800"
        elif t['done']:
            text = loop_pfx + base + chain_sfx; fg = "#883333"
        else:
            text = loop_pfx + base + chain_sfx; fg = "#404040"

        widget['display'].configure(text=text, text_color=fg)

        # Amber tint for idle+loop (CTkLabel can't mix colours so whole label goes amber)
        if t['loop'] and not t['running'] and not t['paused'] and not t['done'] and not t['waiting_for_chain']:
            widget['display'].configure(text_color="#887700")

    def update_timers(self):
        for i, t in enumerate(self.timers):
            if t['running']:
                remaining = _live_remaining(t)
                t['remaining'] = remaining
                if remaining == 0:
                    self.timer_finished(i)
                elif not self._flashing[i]:
                    self.update_display(i)
        now_ms = int(time.time() * 1000)
        delay  = 1000 - (now_ms % 1000)
        self.root.after(max(delay, 50), self.update_timers)

    def timer_finished(self, index):
        t = self.timers[index]
        t['running']          = False
        t['remaining']        = 0
        self._flashing[index] = True
        if _HAS_WINSOUND:
            _beep_queue.put((self.sound_freqs[index], 300))
        self._screen_flash()
        self._flash(index, steps=6, on_done=lambda: self._post_flash(index))

    def _screen_flash(self, alpha=0.18, steps=12, color="#ff6600"):
        """Briefly tint the whole screen with a translucent overlay, then fade out."""
        try:
            sw = self.root.winfo_screenwidth()
            sh = self.root.winfo_screenheight()
            ov = ctk.CTkToplevel(self.root)
            ov.overrideredirect(True)
            ov.attributes('-topmost', True)
            ov.attributes('-alpha', alpha)
            ov.configure(fg_color=color)
            ov.geometry(f"{sw}x{sh}+0+0")
            ov.lift()

            # ── Make the overlay non‑intrusive (Windows) ────────
            try:
                hwnd = ov.winfo_id()
                GWL_EXSTYLE = -20
                WS_EX_NOACTIVATE = 0x08000000   # prevents focus stealing
                WS_EX_TRANSPARENT = 0x00000020  # makes the window click‑through
                style = ctypes.windll.user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
                ctypes.windll.user32.SetWindowLongW(hwnd, GWL_EXSTYLE,
                                                    style | WS_EX_NOACTIVATE | WS_EX_TRANSPARENT)
            except Exception:
                pass   # silently ignore if not on Windows
            # ────────────────────────────────────────────────────

            step_ms = 30
            def fade(remaining_steps):
                if remaining_steps <= 0:
                    try: ov.destroy()
                    except Exception: pass
                    return
                try:
                    new_alpha = alpha * (remaining_steps / steps)
                    ov.attributes('-alpha', new_alpha)
                    self.root.after(step_ms, lambda: fade(remaining_steps - 1))
                except Exception:
                    try: ov.destroy()
                    except Exception: pass

            self.root.after(step_ms, lambda: fade(steps - 1))
        except Exception:
            pass

    def _flash(self, index, steps, on_done):
        if steps <= 0:
            self._flashing[index] = False
            on_done(); return
        color = "#ff0000" if steps % 2 == 0 else "#404040"
        self.timer_widgets[index]['display'].configure(text_color=color)
        self.root.after(100, lambda: self._flash(index, steps - 1, on_done))

    def _post_flash(self, index):
        t = self.timers[index]

        chained = False
        if t['chain_to'] is not None:
            ci = t['chain_to']
            if 0 <= ci < 5:
                nt = self.timers[ci]
                if nt['duration'] > 0 and not nt['running']:
                    nt['remaining'] = nt['remaining_at_start'] = nt['duration']
                    nt['start_wall']        = time.time()
                    nt['running']           = True
                    nt['waiting_for_chain'] = False
                    nt['done']              = False   # clear any stale done state
                    self.update_display(ci)
                    chained = True
                elif nt['running']:
                    self.show_toast(f"T{ci+1} already running — chain skipped")
                else:
                    self.show_toast(f"T{ci+1} was cleared — chain skipped")

        if t['loop'] and t['duration'] > 0 and not chained:
            # Loop restart: source timer runs again
            t['remaining'] = t['remaining_at_start'] = t['duration']
            t['start_wall'] = time.time()
            t['running']    = True
            t['done']       = False
        elif chained:
            # #18: source that chained out goes to idle (not done — it's not finished, it handed off)
            t['done'] = False
        else:
            # No loop, no chain: mark done for the dim-red glow
            t['done'] = True

        self._session_dirty = True
        self.update_display(index)

    # ─────────────────────────────────────────────
    # Window drag
    # ─────────────────────────────────────────────

    def handle_drag_click(self, event):
        if self._drag_click_id is not None:
            self.root.after_cancel(self._drag_click_id)
            self._drag_click_id = None
        self.drag_start_x = event.x_root; self.drag_start_y = event.y_root
        self.drag_x       = event.x;      self.drag_y       = event.y
        self.drag_moved   = False
        self.click_time   = time.time()

    def on_drag(self, event):
        if abs(event.x_root - self.drag_start_x) > 3 or abs(event.y_root - self.drag_start_y) > 3:
            self.drag_moved = True
            x = self.root.winfo_x() + event.x - self.drag_x
            y = self.root.winfo_y() + event.y - self.drag_y
            sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
            ww, wh = self.root.winfo_width(),       self.root.winfo_height()
            snap = 10
            x = 0 if x < snap else (sw - ww if x + ww > sw - snap else x)
            y = 0 if y < snap else (sh - wh if y + wh > sh - snap else y)
            self.root.geometry(f"+{x}+{y}")

    def handle_drag_release(self, event):
        if not self.drag_moved:
            self._drag_click_id = self.root.after(150, self.check_single_click)

    def check_single_click(self):
        self._drag_click_id = None
        if self.click_time != float('inf'):
            self.show_menu()

    def on_double_click(self, event):
        if self._drag_click_id is not None:
            self.root.after_cancel(self._drag_click_id)
            self._drag_click_id = None
        self.click_time = float('inf'); self.drag_moved = True
        self.toggle_collapse()

    def toggle_collapse(self):
        if self.is_collapsed:
            self.timer_row.pack(side='left'); self.is_collapsed = False
        else:
            self.timer_row.pack_forget(); self.is_collapsed = True
        self._session_dirty = True

    # ─────────────────────────────────────────────
    # Volume control  (#3: boolean guard on toast)
    # ─────────────────────────────────────────────

    def _detect_headphones(self):
        """Return True=headphones, False=speakers/other, None=unknown.

        Calls IMMDeviceEnumerator.GetDefaultAudioEndpoint directly so that
        nircmd device switches (which update the Windows default endpoint but
        don't change what AudioUtilities.GetSpeakers() returns in older pycaw
        versions) are always reflected correctly.
        """
        try:
            import comtypes
            from comtypes import CLSCTX_ALL, CoCreateInstance
            from pycaw.pycaw import AudioUtilities

            dev_id = None

            # ── Method A: IMMDeviceEnumerator (new pycaw exports these) ────────
            try:
                from pycaw.pycaw import CLSID_MMDeviceEnumerator, IMMDeviceEnumerator
                enumerator = CoCreateInstance(
                    CLSID_MMDeviceEnumerator, IMMDeviceEnumerator, CLSCTX_ALL)
                device = enumerator.GetDefaultAudioEndpoint(0, 0)  # eRender, eConsole
                raw    = device.GetId()
                dev_id = raw if isinstance(raw, str) else getattr(raw, 'value', None)
                dev_id = (dev_id or '').strip()
            except Exception:
                pass

            # ── Method B: GetSpeakers() — works on new pycaw, may give stale  ──
            # result on old pycaw, but worth trying if Method A failed
            if not dev_id:
                try:
                    speakers = AudioUtilities.GetSpeakers()
                    # Old pycaw: GetSpeakers() returns an AudioDevice with FriendlyName
                    if hasattr(speakers, 'FriendlyName') and speakers.FriendlyName:
                        name = speakers.FriendlyName.lower()
                        return any(k in name for k in
                                   ('headphone', 'headset', 'earphone', 'earbuds'))
                    # New pycaw: GetSpeakers() returns raw IMMDevice
                    dev_obj = getattr(speakers, '_dev', speakers)
                    raw     = dev_obj.GetId()
                    dev_id  = raw if isinstance(raw, str) else getattr(raw, 'value', None)
                    dev_id  = (dev_id or '').strip()
                except Exception:
                    pass

            # ── Match device ID against GetAllDevices() to get FriendlyName ───
            if dev_id:
                for d in AudioUtilities.GetAllDevices():
                    d_id = (d.id or '').strip()
                    if d_id.lower() == dev_id.lower():
                        name = (d.FriendlyName or '').lower()
                        return any(k in name for k in
                                   ('headphone', 'headset', 'earphone', 'earbuds'))
                # Substring fallback (handles minor ID formatting differences)
                for d in AudioUtilities.GetAllDevices():
                    d_id = (d.id or '').strip()
                    if d_id and (d_id.lower() in dev_id.lower()
                                 or dev_id.lower() in d_id.lower()):
                        name = (d.FriendlyName or '').lower()
                        return any(k in name for k in
                                   ('headphone', 'headset', 'earphone', 'earbuds'))

            return None
        except Exception:
            return None

    def _volume_handle_color(self):
        """Background colour for the volume drag handle based on current device type."""
        if self._volume_unavailable:
            return "#555555"
        if self._is_headphones is True:
            return "#66AAFF"   # blue  → headphones
        return "#cc7722"       # orange → speakers / unknown

    def _get_volume_interface(self):
        if self._volume_unavailable: return None
        try:
            import comtypes
            from pycaw.pycaw import AudioUtilities, IAudioEndpointVolume
            from ctypes import cast, POINTER
            devices = AudioUtilities.GetSpeakers()
            device  = devices._dev if hasattr(devices, '_dev') else devices
            iface   = device.Activate(IAudioEndpointVolume._iid_, comtypes.CLSCTX_ALL, None)
            return cast(iface, POINTER(IAudioEndpointVolume))
        except Exception:
            self._volume_unavailable = True
            try: self.drag_handle.configure(fg_color=self._volume_handle_color(), text="--")
            except Exception: pass
            self.show_toast("Volume control unavailable")
            return None

    def get_system_volume(self):
        vol = self._get_volume_interface()
        if vol is None: return 50
        try:    return int(round(vol.GetMasterVolumeLevelScalar() * 100))
        except: self._volume_interface = None; return 50

    def set_system_volume(self, level):
        vol = self._get_volume_interface()
        if vol is None: return None
        try:
            level = int(max(0, min(100, level)))
            vol.SetMasterVolumeLevelScalar(level / 100.0, None)
            return int(round(vol.GetMasterVolumeLevelScalar() * 100))
        except: self._volume_interface = None; return None

    def start_volume_drag(self, event):
        self.volume_start_x = event.x_root; self.volume_start_vol = self.get_system_volume()
        self.last_set_volume = self.volume_start_vol; self.volume_dragging = False
        self.manual_volume_control = True

    def on_volume_drag(self, event):
        delta_px = event.x_root - self.volume_start_x
        if abs(delta_px) > 5:
            if not self.volume_dragging:
                self.volume_dragging = True; self.create_volume_toast()
            new_vol = int(max(0, min(100, self.volume_start_vol + delta_px / 2.0)))
            actual  = self.set_system_volume(new_vol)
            self.last_set_volume = actual if actual is not None else new_vol
            self.update_volume_toast(self.last_set_volume)
            self.drag_handle.configure(text=str(self.last_set_volume))
            self.drag_handle.update_idletasks()

    def end_volume_drag(self, event):
        if self.volume_dragging:
            self.volume_dragging = False
            self.root.after(800, self.hide_volume_toast)
            if self.last_set_volume is not None:
                self.drag_handle.configure(text=str(self.last_set_volume))
            self.root.after(20000, lambda: setattr(self, 'manual_volume_control', False))
        else:
            self.manual_volume_control = False

    def create_volume_toast(self):
        # #3: boolean guard prevents duplicate toplevels on fast motion events
        if self._volume_toast_alive:
            return
        self._volume_toast_alive = True
        self.volume_toast = ctk.CTkToplevel(self.root)
        self.volume_toast.attributes('-topmost', True)
        self.volume_toast.overrideredirect(True)
        self.volume_toast.attributes('-alpha', 0.9)
        frame = ctk.CTkFrame(self.volume_toast, fg_color="#2a2a2a", corner_radius=4)
        frame.pack(padx=3, pady=3, fill='both', expand=True)
        self.volume_label = ctk.CTkLabel(frame, text="Volume: 100%",
                                          font=("Arial", 16, "bold"),
                                          text_color="#ffffff", width=133)
        self.volume_label.pack(padx=16, pady=8)
        self.root.update_idletasks()
        self.volume_toast.geometry(f"+{self.root.winfo_x()+10}+{self.root.winfo_y()+30}")

    def update_volume_toast(self, volume):
        if self.volume_toast and self._volume_toast_alive:
            try: self.volume_label.configure(text=f"Volume: {volume}%")
            except Exception: pass

    def hide_volume_toast(self):
        self._volume_toast_alive = False
        if self.volume_toast:
            try:
                if self.volume_toast.winfo_exists(): self.volume_toast.destroy()
            except Exception: pass
            finally: self.volume_toast = None

    def update_volume_display(self):
        # Reset unavailable flag each poll — device may have changed since last failure
        self._volume_unavailable = False

        # Detect device type and update handle colour when it changes
        detected = self._detect_headphones()
        if detected != self._is_headphones:
            self._is_headphones = detected
            try: self.drag_handle.configure(fg_color=self._volume_handle_color())
            except Exception: pass

        if not self.manual_volume_control and not self.volume_dragging:
            try:
                vol = self.get_system_volume()
                self.drag_handle.configure(text=str(vol))
            except Exception: pass
        elif self.last_set_volume is not None:
            self.drag_handle.configure(text=str(self.last_set_volume))
        self.root.after(2000, self.update_volume_display)

    # ─────────────────────────────────────────────
    # Clock  (#7: single datetime.now() call)
    # ─────────────────────────────────────────────

    def update_clock(self):
        now = datetime.now()   # #7: one call, used for both label and delay
        try: self.datetime_handle.configure(text=now.strftime("%a %d %H:%M"))
        except Exception: pass
        delay = (60 - now.second) * 1000 - now.microsecond // 1000
        self.root.after(max(delay, 100), self.update_clock)

    # ─────────────────────────────────────────────
    # Toast
    # ─────────────────────────────────────────────

    def show_toast(self, message):
        self._toast_queue.append(message)
        if self._toast_window is None or not self._toast_window.winfo_exists():
            self._spawn_toast()
        else:
            self._update_toast_text()

    def _spawn_toast(self):
        if not self._toast_queue: return
        msg = self._toast_queue.pop(0)
        try:
            if self._toast_after_id:
                self.root.after_cancel(self._toast_after_id); self._toast_after_id = None
            if self._toast_window and self._toast_window.winfo_exists():
                self._toast_window.destroy()
        except Exception: pass

        self._toast_window = ctk.CTkToplevel(self.root)
        self._toast_window.attributes('-topmost', True)
        self._toast_window.overrideredirect(True)
        frame = ctk.CTkFrame(self._toast_window, fg_color="#2a2a2a")
        frame.pack(padx=2, pady=2)
        self._toast_label = ctk.CTkLabel(frame, text=msg, font=("Arial", 9))
        self._toast_label.pack(padx=10, pady=5)
        x = self.root.winfo_x()
        y = self.root.winfo_y() - 40
        if y < 0: y = self.root.winfo_y() + self.root.winfo_height() + 5
        self._toast_window.geometry(f"+{x}+{y}")
        self._toast_after_id = self.root.after(1500, self._advance_toast)

    def _update_toast_text(self):
        if not self._toast_queue: return
        msg = self._toast_queue.pop(0)
        try:
            self._toast_label.configure(text=msg)
            if self._toast_after_id: self.root.after_cancel(self._toast_after_id)
            self._toast_after_id = self.root.after(1500, self._advance_toast)
        except Exception: self._spawn_toast()

    def _advance_toast(self):
        self._toast_after_id = None
        if self._toast_queue:
            self._spawn_toast()
        else:
            try:
                if self._toast_window and self._toast_window.winfo_exists():
                    self._toast_window.destroy()
            except Exception: pass
            self._toast_window = None

    # ─────────────────────────────────────────────
    # Context menu  (#4: singleton guard)
    # ─────────────────────────────────────────────

    def show_menu(self, event=None):
        # #4: prevent multiple menus from stacking on rapid clicks
        if self._menu_open:
            return
        self._menu_open = True

        win, _destroy = self._make_popup()   # #12

        def safe_destroy():
            self._menu_open = False
            _destroy()

        frame = ctk.CTkFrame(win, fg_color="#2a2a2a")
        frame.pack(padx=1, pady=1)

        header = self.active_group if self.active_group else "Options"
        ctk.CTkLabel(frame, text=header, font=("Arial", 9, "bold"),
                     text_color="#aaaaaa").pack(padx=5, pady=(4, 2))

        count_frame = ctk.CTkFrame(frame, fg_color="transparent")
        count_frame.pack(padx=5, pady=5)
        ctk.CTkLabel(count_frame, text="Timers:", font=("Arial", 9)).pack(side='left', padx=2)
        for c in [1, 2, 3, 4, 5]:
            ctk.CTkButton(count_frame, text=str(c), width=30, height=20,
                          command=lambda n=c, m=safe_destroy: self.set_visible_timers(n, m),
                          fg_color="#3a3a3a", font=("Arial", 9)).pack(side='left', padx=1)

        pos_frame = ctk.CTkFrame(frame, fg_color="transparent")
        pos_frame.pack(padx=5, pady=5)
        ctk.CTkLabel(pos_frame, text="Position:", font=("Arial", 9)).pack(anchor='w', padx=2)
        for slot in [1, 2]:
            pr = ctk.CTkFrame(pos_frame, fg_color="transparent")
            pr.pack(fill='x', pady=1)
            ctk.CTkButton(pr, text=f"Save Pos {slot}", width=70, height=20,
                          command=lambda s=slot, m=safe_destroy: self.save_position(s, m),
                          fg_color="#3a3a3a", font=("Arial", 9)).pack(side='left', padx=1)
            ctk.CTkButton(pr, text=f"Go Pos {slot}", width=70, height=20,
                          command=lambda s=slot, m=safe_destroy: self.recall_position(s, m),
                          fg_color="#3a3a3a", font=("Arial", 9)).pack(side='left', padx=1)

        for label, cmd, color, hover in [
            ("Groups...",        lambda m=safe_destroy: self.show_groups_manager(m),  "#334433", "#446644"),
            ("Set chains...",    lambda m=safe_destroy: self.show_chain_editor(m),    "#334444", "#446666"),
            ("Manage presets...",lambda m=safe_destroy: self.show_presets_manager(m), "#333344", "#444466"),
            ("Sounds...",        lambda m=safe_destroy: self.show_sounds_editor(m),   "#443333", "#664444"),
            ("Clear session",    lambda m=safe_destroy: self.clear_session(m),        "#443322", "#665533"),
            ("Exit",             lambda m=safe_destroy: (m(), self.quit_app()),         "#cc3333", "#ff4444"),
        ]:
            ctk.CTkButton(frame, text=label, height=20,
                          command=cmd, fg_color=color, hover_color=hover,
                          font=("Arial", 9)).pack(padx=5, pady=(2, 0), fill='x')

        ctk.CTkFrame(frame, height=2, fg_color="transparent").pack()

        self.root.update_idletasks(); win.update_idletasks()
        mx, my = self.root.winfo_pointerx(), self.root.winfo_pointery()
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        mw, mh = win.winfo_reqwidth(), win.winfo_reqheight()
        win.geometry(f"+{min(mx, sw-mw)}+{min(my, sh-mh)}")

        def _mfo(e):
            try:    fw = win.focus_get()
            except: fw = None
            if fw is None: safe_destroy()

        win.bind("<FocusOut>", _mfo)
        try: win.focus_force()
        except Exception: pass

    def save_position(self, slot, menu_close=None):
        x, y = self.root.winfo_x(), self.root.winfo_y()
        self.config['saved_positions'][f'pos{slot}'] = {'x': x, 'y': y}
        self.save_config(); self.show_toast(f"Position {slot} saved!")
        if menu_close: menu_close()

    def recall_position(self, slot, menu_close=None):
        pos = self.config['saved_positions'].get(f'pos{slot}')
        if pos: self.root.geometry(f"+{pos['x']}+{pos['y']}"); self.show_toast(f"Moved to Position {slot}")
        else:   self.show_toast(f"Position {slot} not saved yet")
        if menu_close: menu_close()

    def set_visible_timers(self, count, menu_close=None):
        self.visible_timers = count
        for i in range(5):
            if i < count: self.timer_widgets[i]['frame'].pack(side='left', padx=0)
            else:         self.timer_widgets[i]['frame'].pack_forget()
        self._session_dirty = True
        if menu_close: menu_close()

    def load_group(self, group_name, menu_close=None):
        durations = self.config['groups'].get(group_name, [])
        new_count = min(len(durations), 5)
        self.set_visible_timers(new_count)
        self.active_group = group_name

        for i in range(new_count, 5):
            t = self.timers[i]
            t.update({'remaining': 0, 'remaining_at_start': 0, 'start_wall': 0.0,
                      'duration': 0, 'running': False, 'paused': False,
                      'waiting_for_chain': False, 'loop': False,
                      'chain_to': None, 'done': False})
            self.update_display(i)

        chain_targets = {tc['chain_to'] for tc in durations[:5]
                         if isinstance(tc, dict) and tc.get('chain_to') is not None}

        for i, tc in enumerate(durations[:new_count]):
            if isinstance(tc, dict):
                dur_str, should_loop, chain_to = tc.get('time',''), tc.get('loop',False), tc.get('chain_to',None)
            else:
                dur_str, should_loop, chain_to = tc, False, None

            seconds = self.parse_duration(dur_str)
            if seconds and seconds > 0:
                if i in chain_targets:
                    t = self.timers[i]
                    # #5: done:False also here for chain-target timers
                    t.update({'duration': seconds, 'remaining': 0, 'running': False,
                               'paused': False, 'waiting_for_chain': True, 'done': False})
                else:
                    self.start_timer(i, seconds)
                    self.timers[i]['waiting_for_chain'] = False
                self.timers[i]['loop']     = should_loop
                self.timers[i]['chain_to'] = chain_to
                self.update_display(i)
            else:
                self.show_toast(f"T{i+1}: unrecognised duration '{dur_str}' — skipped")

        self._session_dirty = True
        self.show_toast(f"Loaded '{group_name}'")   # #8: feedback toast
        if menu_close: menu_close()

    def _delete_group(self, group_name, menu_close=None):
        if menu_close: menu_close()
        groups = self.config.get('groups', {})
        if group_name in groups:
            del groups[group_name]; self.save_config()
            if self.active_group == group_name: self.active_group = None
            self.show_toast(f"Deleted '{group_name}'")

    def clear_session(self, menu_close=None):
        if menu_close: menu_close()
        for i in range(5): self.clear_timer(i)
        self.active_group = None
        try:
            if os.path.exists(self.session_file): os.remove(self.session_file)
        except Exception: pass
        self._session_dirty = False   # don't let autosave recreate the file we just deleted
        self.show_toast("Session cleared")

    # ─────────────────────────────────────────────
    # Chain editor
    # ─────────────────────────────────────────────

    def show_chain_editor(self, menu_close=None):
        if menu_close: menu_close()
        win, destroy = self._make_popup()   # #12

        outer = ctk.CTkFrame(win, fg_color="#2a2a2a", corner_radius=4)
        outer.pack(padx=2, pady=2)

        ctk.CTkLabel(outer, text="Chains & loops", font=("Arial", 9, "bold"),
                     text_color="#aaaaaa").pack(pady=(4, 1))

        hdr = ctk.CTkFrame(outer, fg_color="transparent")
        hdr.pack(fill='x', padx=8)
        ctk.CTkLabel(hdr, text="", width=24, font=("Arial", 8)).pack(side='left')
        ctk.CTkLabel(hdr, text="chains to", width=70, font=("Arial", 8),
                     text_color="#666666").pack(side='left', padx=4)
        ctk.CTkLabel(hdr, text="loop", width=36, font=("Arial", 8),
                     text_color="#666666").pack(side='left')

        none_opt   = "None"
        chain_vars = []
        loop_vars  = []

        for i in range(self.visible_timers):
            row = ctk.CTkFrame(outer, fg_color="transparent")
            row.pack(fill='x', padx=8, pady=2)
            ctk.CTkLabel(row, text=f"T{i+1}:", font=("Arial", 9),
                         width=24, anchor='w').pack(side='left')

            opts    = [none_opt] + [f"T{j+1}" for j in range(self.visible_timers) if j != i]
            current = self.timers[i]['chain_to']
            default = f"T{current+1}" if (current is not None and 0 <= current < self.visible_timers
                                           and current != i) else none_opt
            cvar = ctk.StringVar(value=default); chain_vars.append(cvar)
            ctk.CTkOptionMenu(row, variable=cvar, values=opts, width=70, height=18,
                              font=("Arial", 9), fg_color="#3a3a3a", button_color="#444444",
                              dropdown_fg_color="#2a2a2a", dropdown_font=("Arial", 9)
                              ).pack(side='left', padx=4)

            lvar = ctk.BooleanVar(value=self.timers[i]['loop']); loop_vars.append(lvar)
            ctk.CTkCheckBox(row, variable=lvar, text="", width=36, height=18,
                            checkbox_width=14, checkbox_height=14,
                            fg_color="#887700", hover_color="#aa9900"
                            ).pack(side='left')

        def apply_all():
            for i, (cvar, lvar) in enumerate(zip(chain_vars, loop_vars)):
                val = cvar.get()
                self.timers[i]['chain_to'] = None if val == none_opt else int(val[1:]) - 1
                self.timers[i]['loop']     = lvar.get()
                self.update_display(i)
            self._session_dirty = True
            self.show_toast("Chains & loops updated")
            destroy()

        ctk.CTkButton(outer, text="Apply", height=20,
                      font=("Arial", 9), fg_color="#334444", hover_color="#446666",
                      command=apply_all).pack(padx=8, pady=(8, 2), fill='x')
        ctk.CTkButton(outer, text="Cancel", height=20,
                      font=("Arial", 9), fg_color="#3a3a3a",
                      command=destroy).pack(padx=8, pady=(0, 6), fill='x')

        self.root.update_idletasks(); win.update_idletasks()
        x, y = self.root.winfo_pointerx(), self.root.winfo_pointery()
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        win.geometry(f"+{min(x, sw-win.winfo_reqwidth())}+{min(y, sh-win.winfo_reqheight())}")

        def _fo(e):
            try:    fw = win.focus_get()
            except: fw = None
            if fw is None: destroy()

        win.bind('<FocusOut>', _fo)
        try: win.focus_force()
        except Exception: pass

    # ─────────────────────────────────────────────
    # Sounds editor  (#15: respects visible_timers)
    # ─────────────────────────────────────────────

    def show_sounds_editor(self, menu_close=None):
        if menu_close: menu_close()
        win, destroy = self._make_popup()   # #12

        outer = ctk.CTkFrame(win, fg_color="#2a2a2a", corner_radius=4)
        outer.pack(padx=2, pady=2)
        ctk.CTkLabel(outer, text="Beep frequencies (Hz)", font=("Arial", 9, "bold"),
                     text_color="#aaaaaa").pack(pady=(4, 4))

        hz_vars = []
        keys    = ['timer1_hz','timer2_hz','timer3_hz','timer4_hz','timer5_hz']
        s       = self.config.get('sounds', {})

        # #15: always show all 5 but dim inactive rows
        for i in range(5):
            active = (i < self.visible_timers)
            row = ctk.CTkFrame(outer, fg_color="transparent")
            row.pack(fill='x', padx=8, pady=2)
            ctk.CTkLabel(row, text=f"T{i+1}:", font=("Arial", 9),
                         width=24, anchor='w',
                         text_color="#aaaaaa" if active else "#555555").pack(side='left')
            var = ctk.StringVar(value=str(s.get(keys[i], self.sound_freqs[i])))
            hz_vars.append(var)
            entry = ctk.CTkEntry(row, textvariable=var, width=60, height=18,
                                 font=("Consolas", 11),
                                 fg_color="#3a3a3a" if active else "#2a2a2a",
                                 border_width=0, corner_radius=2,
                                 state="normal" if active else "disabled")
            entry.pack(side='left', padx=4)
            ctk.CTkButton(row, text="test", width=36, height=18, font=("Arial", 8),
                          fg_color="#333344" if active else "#2a2a2a",
                          state="normal" if active else "disabled",
                          command=lambda v=var, idx=i: self._test_beep(idx, v)
                          ).pack(side='left')

        def apply_sounds():
            sd = self.config.setdefault('sounds', {})
            for i, var in enumerate(hz_vars):
                if i >= self.visible_timers:
                    continue   # don't save disabled rows
                try:
                    hz = int(var.get().strip())
                    hz = max(37, min(32767, hz))
                    sd[keys[i]]         = hz
                    self.sound_freqs[i] = hz
                except ValueError:
                    pass
            self.save_config(); self.show_toast("Sounds saved"); destroy()

        ctk.CTkButton(outer, text="Apply", height=20,
                      font=("Arial", 9), fg_color="#334444", hover_color="#446666",
                      command=apply_sounds).pack(padx=8, pady=(8, 2), fill='x')
        ctk.CTkButton(outer, text="Cancel", height=20, font=("Arial", 9),
                      fg_color="#3a3a3a", command=destroy).pack(padx=8, pady=(0, 6), fill='x')

        self.root.update_idletasks(); win.update_idletasks()
        x, y = self.root.winfo_pointerx(), self.root.winfo_pointery()
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        win.geometry(f"+{min(x, sw-win.winfo_reqwidth())}+{min(y, sh-win.winfo_reqheight())}")

        def _fo(e):
            try:    fw = win.focus_get()
            except: fw = None
            if fw is None: destroy()

        win.bind('<FocusOut>', _fo)
        try: win.focus_force()
        except Exception: pass

    def _test_beep(self, index, var):
        if not _HAS_WINSOUND:
            self.show_toast("Beep not available on this platform"); return
        try:
            hz = int(var.get().strip()); hz = max(37, min(32767, hz))
            _beep_queue.put((hz, 200))
        except ValueError:
            self.show_toast("Invalid Hz value")

    # ─────────────────────────────────────────────
    # Groups manager  — list, reorder, edit, create
    # ─────────────────────────────────────────────

    def show_groups_manager(self, menu_close=None):
        if menu_close: menu_close()
        win, destroy = self._make_popup()

        outer = ctk.CTkFrame(win, fg_color="#2a2a2a", corner_radius=4)
        outer.pack(padx=2, pady=2)
        ctk.CTkLabel(outer, text="Groups", font=("Arial", 9, "bold"),
                     text_color="#aaaaaa").pack(pady=(4, 2))

        list_frame = ctk.CTkFrame(outer, fg_color="transparent")
        list_frame.pack(padx=5, fill='x')

        def rebuild():
            for w in list_frame.winfo_children(): w.destroy()
            groups = self.config.get('groups', {})
            names  = list(groups.keys())
            if not names:
                ctk.CTkLabel(list_frame, text="No groups yet", font=("Arial", 9),
                             text_color="#555555").pack(pady=4)
                return
            for idx, gname in enumerate(names):
                row = ctk.CTkFrame(list_frame, fg_color="#333333", corner_radius=2)
                row.pack(fill='x', pady=1)

                # Up / Down arrows stacked on the left
                arr = ctk.CTkFrame(row, fg_color="transparent")
                arr.pack(side='left', padx=(3, 0))
                ctk.CTkButton(arr, text="↑", width=18, height=11, font=("Arial", 7),
                              fg_color="#3a3a3a", hover_color="#555555",
                              command=lambda g=gname: (move_group(g, -1), rebuild())
                              ).pack(pady=(1, 0))
                ctk.CTkButton(arr, text="↓", width=18, height=11, font=("Arial", 7),
                              fg_color="#3a3a3a", hover_color="#555555",
                              command=lambda g=gname: (move_group(g, +1), rebuild())
                              ).pack(pady=(0, 1))

                # Group name label — expand to fill
                active_mark = " ●" if gname == self.active_group else ""
                ctk.CTkLabel(row, text=gname + active_mark, font=("Arial", 9), anchor='w'
                             ).pack(side='left', padx=5, fill='x', expand=True)

                # Action buttons
                ctk.CTkButton(row, text="Load", width=38, height=20, font=("Arial", 8),
                              fg_color="#334433", hover_color="#446644",
                              command=lambda g=gname: load_and_close(g)
                              ).pack(side='left', padx=1)
                ctk.CTkButton(row, text="Edit", width=38, height=20, font=("Arial", 8),
                              fg_color="#334444", hover_color="#446666",
                              command=lambda g=gname: self._open_group_editor(g, on_save=rebuild)
                              ).pack(side='left', padx=1)
                ctk.CTkButton(row, text="×", width=22, height=20, font=("Arial", 9),
                              fg_color="#552222", hover_color="#883333",
                              command=lambda g=gname: delete_group(g)
                              ).pack(side='left', padx=(1, 4))

        def move_group(name, direction):
            groups = self.config.get('groups', {})
            names  = list(groups.keys())
            if name not in names: return
            idx     = names.index(name)
            new_idx = idx + direction
            if not (0 <= new_idx < len(names)): return
            names.insert(new_idx, names.pop(idx))
            self.config['groups'] = {n: groups[n] for n in names}
            self.save_config()

        def delete_group(name):
            groups = self.config.get('groups', {})
            if name in groups:
                del groups[name]; self.save_config()
                if self.active_group == name: self.active_group = None
                self.show_toast(f"Deleted '{name}'")
            rebuild()

        def load_and_close(name):
            self.load_group(name); destroy()

        rebuild()

        ctk.CTkFrame(outer, fg_color="#444444", height=1).pack(fill='x', padx=5, pady=4)

        btn_row = ctk.CTkFrame(outer, fg_color="transparent")
        btn_row.pack(padx=5, pady=(0, 2), fill='x')

        def open_save_current():
            # Build prefill from current timer state
            entries = []
            for i in range(self.visible_timers):
                t = self.timers[i]
                if t['duration'] > 0:
                    entries.append({'time': _fmt_label(t['duration']),
                                    'loop': t['loop'], 'chain_to': t['chain_to']})
            if not entries:
                self.show_toast("No timers set to save"); return
            self._open_group_editor(None, prefill=entries, on_save=rebuild)

        ctk.CTkButton(btn_row, text="New group", height=20, font=("Arial", 9),
                      fg_color="#334433", hover_color="#446644",
                      command=lambda: self._open_group_editor(None, on_save=rebuild)
                      ).pack(side='left', fill='x', expand=True, padx=(0, 2))
        ctk.CTkButton(btn_row, text="Save current…", height=20, font=("Arial", 9),
                      fg_color="#333344", hover_color="#444466",
                      command=open_save_current
                      ).pack(side='left', fill='x', expand=True)

        ctk.CTkButton(outer, text="Done", height=20, font=("Arial", 9),
                      fg_color="#3a3a3a", command=destroy
                      ).pack(padx=5, pady=(2, 5), fill='x')

        self.root.update_idletasks(); win.update_idletasks()
        x, y = self.root.winfo_pointerx(), self.root.winfo_pointery()
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        win.geometry(f"+{min(x, sw-win.winfo_reqwidth())}+{min(y, sh-win.winfo_reqheight())}")
        win.bind('<Escape>', lambda e: destroy())
        try: win.focus_force()
        except Exception: pass

    def _open_group_editor(self, group_name=None, prefill=None, on_save=None):
        """Create / edit a group in a dedicated popup.
        group_name=None → new group.  prefill → list of timer dicts to pre-load.
        on_save() is called after a successful save so callers can rebuild their list.
        """
        win, destroy = self._make_popup()

        outer = ctk.CTkFrame(win, fg_color="#2a2a2a", corner_radius=4)
        outer.pack(padx=2, pady=2)

        is_new = group_name is None
        ctk.CTkLabel(outer, text="New group" if is_new else "Edit group",
                     font=("Arial", 9, "bold"), text_color="#aaaaaa").pack(pady=(4, 2))

        # ── Name row ──────────────────────────────────────────────────────────
        name_row = ctk.CTkFrame(outer, fg_color="transparent")
        name_row.pack(fill='x', padx=8, pady=(0, 4))
        ctk.CTkLabel(name_row, text="Name:", font=("Arial", 9),
                     width=40, anchor='w').pack(side='left')
        name_var = ctk.StringVar(value=group_name or "")
        name_entry = ctk.CTkEntry(name_row, textvariable=name_var, width=130, height=18,
                                   font=("Consolas", 11), fg_color="#3a3a3a",
                                   border_width=0, corner_radius=2)
        name_entry.pack(side='left')

        # ── Header row ────────────────────────────────────────────────────────
        hdr = ctk.CTkFrame(outer, fg_color="transparent")
        hdr.pack(fill='x', padx=8)
        ctk.CTkLabel(hdr, text="Duration", width=74, font=("Arial", 8),
                     text_color="#666666", anchor='w').pack(side='left')
        ctk.CTkLabel(hdr, text="Loop",     width=34, font=("Arial", 8),
                     text_color="#666666").pack(side='left', padx=(4, 0))
        ctk.CTkLabel(hdr, text="Chain to", width=72, font=("Arial", 8),
                     text_color="#666666").pack(side='left', padx=(8, 0))

        # ── Timer rows ────────────────────────────────────────────────────────
        rows_frame = ctk.CTkFrame(outer, fg_color="transparent")
        rows_frame.pack(fill='x', padx=8)

        timer_rows = []   # list of dicts: {frame, time_var, loop_var, chain_var}

        none_opt    = "None"
        chain_opts  = [none_opt] + [f"T{j+1}" for j in range(5)]

        def add_row(data=None):
            if len(timer_rows) >= 5:
                self.show_toast("Maximum 5 timers per group"); return
            data = data or {}
            time_str  = data.get('time', '')  if isinstance(data, dict) else str(data)
            loop_val  = data.get('loop', False) if isinstance(data, dict) else False
            ct        = data.get('chain_to', None) if isinstance(data, dict) else None
            chain_def = f"T{ct+1}" if (ct is not None and 0 <= ct < 5) else none_opt

            time_var  = ctk.StringVar(value=time_str)
            loop_var  = ctk.BooleanVar(value=loop_val)
            chain_var = ctk.StringVar(value=chain_def)

            rf = ctk.CTkFrame(rows_frame, fg_color="#333333", corner_radius=2)
            rf.pack(fill='x', pady=1)

            ctk.CTkEntry(rf, textvariable=time_var, width=74, height=18,
                         font=("Consolas", 11), fg_color="#2a2a2a",
                         border_width=0, corner_radius=2,
                         placeholder_text="5m, 1h30m…"
                         ).pack(side='left', padx=(4, 2), pady=2)

            ctk.CTkCheckBox(rf, variable=loop_var, text="", width=34, height=18,
                            checkbox_width=14, checkbox_height=14,
                            fg_color="#887700", hover_color="#aa9900"
                            ).pack(side='left', padx=4)

            ctk.CTkOptionMenu(rf, variable=chain_var, values=chain_opts,
                              width=72, height=18, font=("Arial", 8),
                              fg_color="#3a3a3a", button_color="#444444",
                              dropdown_fg_color="#2a2a2a", dropdown_font=("Arial", 9)
                              ).pack(side='left', padx=2)

            rd = {'frame': rf, 'time_var': time_var,
                  'loop_var': loop_var, 'chain_var': chain_var}
            timer_rows.append(rd)

            ctk.CTkButton(rf, text="×", width=22, height=18, font=("Arial", 9),
                          fg_color="#552222", hover_color="#883333",
                          command=lambda r=rd: remove_row(r)
                          ).pack(side='left', padx=(2, 4))

            win.update_idletasks()

        def remove_row(rd):
            rd['frame'].destroy(); timer_rows.remove(rd)
            win.update_idletasks()

        # Pre-populate from existing group or prefill
        source = prefill
        if source is None and group_name:
            source = self.config.get('groups', {}).get(group_name, [])
        for entry in (source or []):
            add_row(entry)
        if not timer_rows:
            add_row()   # at least one blank row

        ctk.CTkButton(outer, text="+ Add timer", height=18, font=("Arial", 8),
                      fg_color="#3a3a3a", hover_color="#555555",
                      command=add_row).pack(padx=8, pady=(4, 2), fill='x')

        # ── Apply / Cancel ────────────────────────────────────────────────────
        def apply():
            name = name_var.get().strip()
            if not name:
                self.show_toast("Enter a group name")
                try: name_entry.focus_force()
                except Exception: pass
                return

            groups = self.config.setdefault('groups', {})
            if name != group_name and name in groups:
                self.show_toast(f"'{name}' already exists"); return

            entries = []
            for rd in timer_rows:
                t = rd['time_var'].get().strip()
                if not t: continue
                secs = self.parse_duration(t)
                if not secs or secs <= 0:
                    self.show_toast(f"Invalid duration: '{t}'"); return
                cv       = rd['chain_var'].get()
                chain_to = None if cv == none_opt else int(cv[1:]) - 1
                entries.append({'time': _fmt_label(secs),
                                'loop': rd['loop_var'].get(),
                                'chain_to': chain_to})
            if not entries:
                self.show_toast("Add at least one timer"); return

            if not is_new and group_name != name:
                # Rename in-place to preserve order
                new_groups = {}
                for k, v in groups.items():
                    if k == group_name:
                        new_groups[name] = entries
                    else:
                        new_groups[k] = v
                self.config['groups'] = new_groups
                if self.active_group == group_name:
                    self.active_group = name
            else:
                groups[name] = entries

            self.save_config()
            self.show_toast(f"{'Created' if is_new else 'Updated'} '{name}'")
            if on_save: on_save()
            destroy()

        ctk.CTkButton(outer, text="Save", height=20, font=("Arial", 9),
                      fg_color="#334444", hover_color="#446666",
                      command=apply).pack(padx=8, pady=(6, 2), fill='x')
        ctk.CTkButton(outer, text="Cancel", height=20, font=("Arial", 9),
                      fg_color="#3a3a3a", command=destroy
                      ).pack(padx=8, pady=(0, 6), fill='x')

        self.root.update_idletasks(); win.update_idletasks()
        x, y = self.root.winfo_pointerx(), self.root.winfo_pointery()
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        win.geometry(f"+{min(x, sw-win.winfo_reqwidth())}+{min(y, sh-win.winfo_reqheight())}")
        win.bind('<Escape>', lambda e: destroy())
        try: name_entry.focus_force()
        except Exception: pass

    # ─────────────────────────────────────────────
    # Save current state as group  (#6: skip 0-duration timers)
    # ─────────────────────────────────────────────

    def save_current_as_group(self, menu_close=None):
        if menu_close: menu_close()
        if not any(self.timers[i]['duration'] > 0 for i in range(self.visible_timers)):
            self.show_toast("No timers set to save"); return

        win, destroy = self._make_popup()   # #12

        frame = ctk.CTkFrame(win, fg_color="#3a3a3a", corner_radius=4)
        frame.pack(padx=2, pady=2)
        ctk.CTkLabel(frame, text="Group name:", font=("Arial", 9),
                     text_color="#aaaaaa").pack(side='left', padx=(6, 2), pady=4)
        name_var = ctk.StringVar()
        entry = ctk.CTkEntry(frame, textvariable=name_var, width=90, height=18,
                             font=("Consolas", 12), fg_color="#2a2a2a",
                             border_width=0, corner_radius=2)
        entry.pack(side='left', padx=(0, 6), pady=4)

        def commit(event=None):
            name = name_var.get().strip()
            if not name: destroy(); return
            if name in self.config.get('groups', {}):
                self.show_toast(f"Group '{name}' already exists")
                try: entry.select_range(0, 'end'); entry.focus_force()
                except Exception: pass
                return
            entries = []
            saved_indices = []
            for i in range(self.visible_timers):
                t = self.timers[i]
                if t['duration'] <= 0:
                    continue
                saved_indices.append(i)
                entries.append({"time": _fmt_label(t['duration']),
                                 "loop": t['loop'], "chain_to": t['chain_to']})
            # Remap chain_to from absolute slot indices to positional indices within saved_indices,
            # and strip any that pointed at a skipped (0-duration) timer.
            pos_map = {orig: pos for pos, orig in enumerate(saved_indices)}
            for saved_entry in entries:
                ct = saved_entry['chain_to']
                saved_entry['chain_to'] = pos_map.get(ct) if ct is not None else None
            self.config.setdefault('groups', {})[name] = entries
            self.save_config(); self.active_group = name
            self.show_toast(f"Saved group '{name}'"); destroy()

        entry.bind('<Return>', commit); entry.bind('<KP_Enter>', commit)
        entry.bind('<Escape>', lambda e: destroy())

        def _fo(e):
            try:    fw = win.focus_get()
            except: fw = None
            if fw is None: destroy()

        win.bind('<FocusOut>', _fo)
        x = self.root.winfo_x(); y = self.root.winfo_y() - 44
        if y < 0: y = self.root.winfo_y() + self.root.winfo_height() + 4
        win.geometry(f"+{x}+{y}")
        try: entry.focus_force()
        except Exception: pass

    # ─────────────────────────────────────────────
    # Presets manager  (#11: uses _add_preset/_remove_preset)
    # ─────────────────────────────────────────────

    def show_presets_manager(self, menu_close=None):
        if menu_close: menu_close()
        win, destroy = self._make_popup()   # #12

        outer = ctk.CTkFrame(win, fg_color="#2a2a2a", corner_radius=4)
        outer.pack(padx=2, pady=2)
        ctk.CTkLabel(outer, text="Presets", font=("Arial", 9, "bold"),
                     text_color="#aaaaaa").pack(pady=(4, 2))

        list_frame = ctk.CTkFrame(outer, fg_color="transparent")
        list_frame.pack(padx=5, fill='x')

        def rebuild_list():
            for w in list_frame.winfo_children(): w.destroy()
            for idx, lbl in enumerate(self.preset_labels):
                row = ctk.CTkFrame(list_frame, fg_color="transparent")
                row.pack(fill='x', pady=1)
                ctk.CTkLabel(row, text=lbl, font=("Arial", 9),
                             width=60, anchor='w').pack(side='left', padx=2)
                ctk.CTkButton(row, text="x", width=22, height=18,
                              font=("Arial", 9), fg_color="#552222", hover_color="#883333",
                              command=lambda i=idx: delete_preset(i)).pack(side='right', padx=2)

        def delete_preset(idx):
            if not (0 <= idx < len(self.preset_labels)):
                return
            self.preset_labels.pop(idx)
            self.preset_values.pop(idx)
            self.config.setdefault('presets', {})['labels']            = self.preset_labels
            self.config['presets']['durations_seconds']                 = self.preset_values
            try:
                self.save_config()
                self.show_toast(f"Preset deleted ({len(self.preset_labels)} remaining)")
            except Exception as e:
                self.show_toast(f"Save failed: {e}")
            self._reload_preset_dropdowns()
            try: rebuild_list()
            except Exception: pass

        rebuild_list()
        ctk.CTkFrame(outer, fg_color="#444444", height=1).pack(fill='x', padx=5, pady=4)

        add_frame = ctk.CTkFrame(outer, fg_color="transparent")
        add_frame.pack(padx=5, pady=(0, 5), fill='x')
        add_var = ctk.StringVar()
        add_entry = ctk.CTkEntry(add_frame, textvariable=add_var, width=80, height=18,
                                 placeholder_text="e.g. 8m",
                                 font=("Consolas", 11), fg_color="#3a3a3a",
                                 border_width=0, corner_radius=2)
        add_entry.pack(side='left', padx=(0, 4))

        def add_preset(event=None):
            secs = self.parse_duration(add_var.get().strip())
            if not secs or secs <= 0: self.show_toast("Invalid duration"); return
            lbl = _fmt_label(secs)
            if lbl in self.preset_labels: self.show_toast(f"{lbl} already exists"); return
            self._add_preset(lbl, secs)   # #11
            self.save_config(); self._reload_preset_dropdowns(); add_var.set(""); rebuild_list()

        ctk.CTkButton(add_frame, text="Add", width=40, height=18,
                      font=("Arial", 9), fg_color="#3a3a3a",
                      command=add_preset).pack(side='left')
        add_entry.bind('<Return>', add_preset); add_entry.bind('<KP_Enter>', add_preset)
        ctk.CTkButton(outer, text="Done", height=20, font=("Arial", 9),
                      fg_color="#3a3a3a", command=destroy).pack(padx=5, pady=(2, 5), fill='x')

        self.root.update_idletasks(); win.update_idletasks()
        x, y = self.root.winfo_pointerx(), self.root.winfo_pointery()
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        win.geometry(f"+{min(x, sw-win.winfo_reqwidth())}+{min(y, sh-win.winfo_reqheight())}")

        add_entry.bind('<Escape>', lambda e: destroy())
        win.bind('<Escape>', lambda e: destroy())
        try: add_entry.focus_force()
        except Exception: pass

    # ─────────────────────────────────────────────
    # Parse duration  (#13: bare integer treated as minutes)
    # ─────────────────────────────────────────────

    def parse_duration(self, s):
        s = str(s).strip().lower()
        m = re.match(r'^(\d+):(\d{2}):(\d{2})$', s)
        if m: return int(m.group(1))*3600 + int(m.group(2))*60 + int(m.group(3))
        m = re.match(r'^(\d+):(\d{2})$', s)
        if m: return int(m.group(1))*60 + int(m.group(2))
        total, found = 0, False
        for num, unit in re.findall(r'(\d+)([hms])', s):
            found = True; n = int(num)
            if unit == 'h': total += n*3600
            elif unit == 'm': total += n*60
            elif unit == 's': total += n
        if found: return total
        # #13: bare integer → minutes (typing "5" gives 5 minutes, not 5 seconds)
        m = re.match(r'^(\d+)$', s)
        if m: return int(m.group(1)) * 60
        return None

    # ─────────────────────────────────────────────
    # Quit
    # ─────────────────────────────────────────────

    def quit_app(self):
        self.config['window_x'] = self.root.winfo_x()
        self.config['window_y'] = self.root.winfo_y()
        try: self.save_config()
        except Exception: pass
        try: self.save_session()
        except Exception: pass
        self.root.quit()

    def run(self):
        self.root.protocol("WM_DELETE_WINDOW", self.quit_app)
        self.root.mainloop()


if __name__ == "__main__":
    app = TimerApp()
    app.run()
