import os
import streamlit as st
import pandas as pd
import requests
import json
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from streamlit_autorefresh import st_autorefresh
from datetime import datetime, timedelta
import re
import threading
import time
import logging
import streamlit.components.v1 as components
import queue
import asyncio
import websockets
import struct
import numpy as np
from collections import deque
from typing import List, Tuple, Dict, Any, Optional

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler("error.log"),
        logging.StreamHandler()
    ]
)

def log_error(message):
    logging.error(message)

# Page configuration
st.set_page_config(
    layout="wide", 
    page_title="ComOflo + Depth Dashboard",
    page_icon="📊"
)

# Auto-refresh controls
refresh_enabled = st.sidebar.toggle('🔄 Auto-refresh', value=True)
refresh_interval = st.sidebar.selectbox('Refresh Interval (seconds)', [5, 10, 15, 30, 60], index=2)
if refresh_enabled:
    st_autorefresh(interval=refresh_interval * 1000, key="data_refresh", limit=None)

# Create local cache directories
LOCAL_CACHE_DIR = "local_cache"
ALERT_CACHE_DIR = "alert_cache"
for directory in [LOCAL_CACHE_DIR, ALERT_CACHE_DIR]:
    if not os.path.exists(directory):
        os.makedirs(directory)

# Configuration
GITHUB_USER = "Vishtheendodoc"
GITHUB_REPO = "ComOflo"
DATA_FOLDER = "data_snapshots"
FLASK_API_BASE = "https://comoflo.onrender.com/api"
STOCK_LIST_FILE = "stock_list.csv"

# Depth WebSocket Configuration
DEPTH_WSS = "wss://depth-api-feed.dhan.co/twentydepth"
DEPTH_20_REQ = 23

# Alert thresholds
ALERT_CONFIG = {
    'large_order_threshold': 1000,
    'imbalance_ratio_threshold': 3.0,
    'spread_compression_threshold': 0.1,
    'iceberg_detection_threshold': 5,
    'volume_spike_threshold': 2.0,
    'price_level_break_threshold': 5,
    'order_flow_momentum_threshold': 0.7,
}

# Telegram configuration
TELEGRAM_BOT_TOKEN = st.secrets.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = st.secrets.get("TELEGRAM_CHAT_ID", "")

# ==================== DEPTH ANALYSIS CLASSES ====================

class AlertEngine:
    """Sophisticated alert detection engine for market depth analysis"""
    
    def __init__(self):
        self.price_history = {}
        self.volume_history = {}
        self.order_flow_history = {}
        self.last_depth = {}
        self.alerts = deque(maxlen=100)
        self.iceberg_tracker = {}
        
    def analyze_depth_and_generate_alerts(self, security_id: str, bid_data: List[Dict], ask_data: List[Dict]) -> List[Dict]:
        """Main analysis function - returns list of alerts for this update"""
        alerts = []
        timestamp = datetime.now()
        
        if security_id not in self.price_history:
            self._initialize_security_tracking(security_id)
            
        metrics = self._calculate_metrics(security_id, bid_data, ask_data)
        
        # Run alert detection algorithms
        alerts.extend(self._detect_large_orders(security_id, bid_data, ask_data, timestamp))
        alerts.extend(self._detect_order_imbalance(security_id, metrics, timestamp))
        alerts.extend(self._detect_spread_compression(security_id, metrics, timestamp))
        alerts.extend(self._detect_volume_spikes(security_id, metrics, timestamp))
        alerts.extend(self._detect_level_breaks(security_id, bid_data, ask_data, timestamp))
        alerts.extend(self._detect_order_flow_momentum(security_id, metrics, timestamp))
        
        self._update_history(security_id, metrics)
        self.last_depth[security_id] = {'bid': bid_data, 'ask': ask_data, 'timestamp': timestamp}
        
        for alert in alerts:
            self.alerts.append(alert)
            
        return alerts
    
    def _initialize_security_tracking(self, security_id: str):
        """Initialize tracking structures for a new security"""
        self.price_history[security_id] = deque(maxlen=100)
        self.volume_history[security_id] = deque(maxlen=100)
        self.order_flow_history[security_id] = deque(maxlen=50)
        self.iceberg_tracker[security_id] = {}
        
    def _calculate_metrics(self, security_id: str, bid_data: List[Dict], ask_data: List[Dict]) -> Dict:
        """Calculate key market microstructure metrics"""
        if not bid_data or not ask_data:
            return {}
            
        best_bid = max(bid_data, key=lambda x: x['price'])
        best_ask = min(ask_data, key=lambda x: x['price'])
        
        spread = best_ask['price'] - best_bid['price']
        mid_price = (best_bid['price'] + best_ask['price']) / 2
        spread_pct = (spread / mid_price) * 100 if mid_price > 0 else 0
        
        total_bid_qty = sum(level['quantity'] for level in bid_data)
        total_ask_qty = sum(level['quantity'] for level in ask_data)
        total_bid_orders = sum(level['orders'] for level in bid_data)
        total_ask_orders = sum(level['orders'] for level in ask_data)
        
        qty_imbalance = (total_bid_qty - total_ask_qty) / (total_bid_qty + total_ask_qty) if (total_bid_qty + total_ask_qty) > 0 else 0
        order_imbalance = (total_bid_orders - total_ask_orders) / (total_bid_orders + total_ask_orders) if (total_bid_orders + total_ask_orders) > 0 else 0
        
        top5_bid_qty = sum(level['quantity'] for level in sorted(bid_data, key=lambda x: x['price'], reverse=True)[:5])
        top5_ask_qty = sum(level['quantity'] for level in sorted(ask_data, key=lambda x: x['price'])[:5])
        
        return {
            'timestamp': datetime.now(),
            'best_bid': best_bid['price'],
            'best_ask': best_ask['price'],
            'spread': spread,
            'spread_pct': spread_pct,
            'mid_price': mid_price,
            'total_bid_qty': total_bid_qty,
            'total_ask_qty': total_ask_qty,
            'total_bid_orders': total_bid_orders,
            'total_ask_orders': total_ask_orders,
            'qty_imbalance': qty_imbalance,
            'order_imbalance': order_imbalance,
            'top5_bid_qty': top5_bid_qty,
            'top5_ask_qty': top5_ask_qty,
        }
    
    def _detect_large_orders(self, security_id: str, bid_data: List[Dict], ask_data: List[Dict], timestamp: datetime) -> List[Dict]:
        """Detect unusually large orders"""
        alerts = []
        threshold = ALERT_CONFIG['large_order_threshold']
        
        for level in bid_data:
            if level['quantity'] >= threshold:
                alerts.append({
                    'type': 'LARGE_BID_ORDER',
                    'security_id': security_id,
                    'timestamp': timestamp,
                    'price': level['price'],
                    'quantity': level['quantity'],
                    'orders': level['orders'],
                    'severity': 'HIGH' if level['quantity'] >= threshold * 2 else 'MEDIUM',
                    'message': f"Large bid order: {level['quantity']} @ {level['price']}"
                })
        
        for level in ask_data:
            if level['quantity'] >= threshold:
                alerts.append({
                    'type': 'LARGE_ASK_ORDER',
                    'security_id': security_id,
                    'timestamp': timestamp,
                    'price': level['price'],
                    'quantity': level['quantity'],
                    'orders': level['orders'],
                    'severity': 'HIGH' if level['quantity'] >= threshold * 2 else 'MEDIUM',
                    'message': f"Large ask order: {level['quantity']} @ {level['price']}"
                })
        
        return alerts
    
    def _detect_order_imbalance(self, security_id: str, metrics: Dict, timestamp: datetime) -> List[Dict]:
        """Detect significant order flow imbalance"""
        alerts = []
        if not metrics:
            return alerts
            
        qty_imbalance = abs(metrics['qty_imbalance'])
        threshold = 1 / ALERT_CONFIG['imbalance_ratio_threshold']
        
        if qty_imbalance > threshold:
            direction = "BUY" if metrics['qty_imbalance'] > 0 else "SELL"
            alerts.append({
                'type': 'ORDER_IMBALANCE',
                'security_id': security_id,
                'timestamp': timestamp,
                'direction': direction,
                'imbalance_ratio': metrics['qty_imbalance'],
                'severity': 'HIGH' if qty_imbalance > threshold * 1.5 else 'MEDIUM',
                'message': f"Strong {direction} imbalance: {qty_imbalance:.2%} quantity imbalance"
            })
        
        return alerts
    
    def _detect_spread_compression(self, security_id: str, metrics: Dict, timestamp: datetime) -> List[Dict]:
        """Detect spread compression"""
        alerts = []
        if not metrics or security_id not in self.price_history:
            return alerts
            
        current_spread_pct = metrics['spread_pct']
        recent_spreads = [m.get('spread_pct', 0) for m in list(self.price_history[security_id])[-15:] if m.get('spread_pct', 0) > 0]
        if len(recent_spreads) < 10:
            return alerts
            
        avg_spread = np.mean(recent_spreads[:-3])
        recent_avg = np.mean(recent_spreads[-3:])
        
        if avg_spread == 0:
            return alerts
            
        compression_ratio = (avg_spread - recent_avg) / avg_spread
        
        if compression_ratio > ALERT_CONFIG['spread_compression_threshold']:
            alerts.append({
                'type': 'SPREAD_COMPRESSION',
                'security_id': security_id,
                'timestamp': timestamp,
                'current_spread': current_spread_pct,
                'avg_spread': avg_spread,
                'compression_ratio': compression_ratio,
                'severity': 'HIGH',
                'message': f"Spread compressing: {compression_ratio:.1%} tighter"
            })
        
        return alerts
    
    def _detect_volume_spikes(self, security_id: str, metrics: Dict, timestamp: datetime) -> List[Dict]:
        """Detect volume spikes compared to recent average"""
        alerts = []
        if not metrics or security_id not in self.volume_history:
            return alerts
            
        current_total_qty = metrics['total_bid_qty'] + metrics['total_ask_qty']
        recent_volumes = [m.get('total_volume', 0) for m in list(self.volume_history[security_id])[-20:]]
        if len(recent_volumes) < 10:
            return alerts
            
        avg_volume = np.mean(recent_volumes)
        if avg_volume == 0:
            return alerts
            
        volume_ratio = current_total_qty / avg_volume
        
        if volume_ratio >= ALERT_CONFIG['volume_spike_threshold']:
            alerts.append({
                'type': 'VOLUME_SPIKE',
                'security_id': security_id,
                'timestamp': timestamp,
                'current_volume': current_total_qty,
                'avg_volume': avg_volume,
                'volume_ratio': volume_ratio,
                'severity': 'HIGH' if volume_ratio >= ALERT_CONFIG['volume_spike_threshold'] * 1.5 else 'MEDIUM',
                'message': f"Volume spike: {volume_ratio:.1f}x average volume"
            })
        
        return alerts
    
    def _detect_level_breaks(self, security_id: str, bid_data: List[Dict], ask_data: List[Dict], timestamp: datetime) -> List[Dict]:
        """Detect when price breaks through multiple levels"""
        alerts = []
        if security_id not in self.last_depth:
            return alerts
            
        last_depth = self.last_depth[security_id]
        if not last_depth or 'bid' not in last_depth or 'ask' not in last_depth:
            return alerts
            
        current_best_bid = max(bid_data, key=lambda x: x['price'])['price'] if bid_data else 0
        current_best_ask = min(ask_data, key=lambda x: x['price'])['price'] if ask_data else float('inf')
        
        prev_best_bid = max(last_depth['bid'], key=lambda x: x['price'])['price'] if last_depth['bid'] else 0
        prev_best_ask = min(last_depth['ask'], key=lambda x: x['price'])['price'] if last_depth['ask'] else float('inf')
        
        if current_best_bid > prev_best_ask:
            levels_broken = len([level for level in last_depth['ask'] if level['price'] <= current_best_bid])
            if levels_broken >= ALERT_CONFIG['price_level_break_threshold']:
                alerts.append({
                    'type': 'UPSIDE_BREAKOUT',
                    'security_id': security_id,
                    'timestamp': timestamp,
                    'levels_broken': levels_broken,
                    'new_price': current_best_bid,
                    'severity': 'HIGH',
                    'message': f"Upside breakout: Broke through {levels_broken} ask levels"
                })
        
        elif current_best_ask < prev_best_bid:
            levels_broken = len([level for level in last_depth['bid'] if level['price'] >= current_best_ask])
            if levels_broken >= ALERT_CONFIG['price_level_break_threshold']:
                alerts.append({
                    'type': 'DOWNSIDE_BREAKOUT',
                    'security_id': security_id,
                    'timestamp': timestamp,
                    'levels_broken': levels_broken,
                    'new_price': current_best_ask,
                    'severity': 'HIGH',
                    'message': f"Downside breakout: Broke through {levels_broken} bid levels"
                })
        
        return alerts
    
    def _detect_order_flow_momentum(self, security_id: str, metrics: Dict, timestamp: datetime) -> List[Dict]:
        """Detect sustained order flow momentum"""
        alerts = []
        if not metrics or security_id not in self.order_flow_history:
            return alerts
            
        recent_imbalances = [m.get('qty_imbalance', 0) for m in list(self.order_flow_history[security_id])[-10:]]
        if len(recent_imbalances) < 5:
            return alerts
            
        avg_imbalance = np.mean(recent_imbalances)
        consistency = len([x for x in recent_imbalances if np.sign(x) == np.sign(avg_imbalance)]) / len(recent_imbalances)
        momentum_score = abs(avg_imbalance) * consistency
        
        if momentum_score >= ALERT_CONFIG['order_flow_momentum_threshold']:
            direction = "BULLISH" if avg_imbalance > 0 else "BEARISH"
            alerts.append({
                'type': 'ORDER_FLOW_MOMENTUM',
                'security_id': security_id,
                'timestamp': timestamp,
                'direction': direction,
                'momentum_score': momentum_score,
                'consistency': consistency,
                'avg_imbalance': avg_imbalance,
                'severity': 'HIGH',
                'message': f"{direction} momentum: {momentum_score:.2f} score, {consistency:.0%} consistency"
            })
        
        return alerts
    
    def _update_history(self, security_id: str, metrics: Dict):
        """Update historical data"""
        if not metrics:
            return
            
        metrics['total_volume'] = metrics['total_bid_qty'] + metrics['total_ask_qty']
        
        self.price_history[security_id].append(metrics)
        self.volume_history[security_id].append(metrics)
        self.order_flow_history[security_id].append(metrics)
    
    def get_recent_alerts(self, limit: int = 20) -> List[Dict]:
        """Get recent alerts sorted by timestamp"""
        return sorted(list(self.alerts)[-limit:], key=lambda x: x['timestamp'], reverse=True)

def parse_header_slice(header_bytes: bytes):
    try:
        return struct.unpack('<hBBiI', header_bytes)
    except Exception:
        return None

def parse_depth_message(raw: bytes):
    if len(raw) < 12:
        return None

    header = parse_header_slice(raw[0:12])
    if not header:
        return None

    msg_length = header[0]
    msg_code = header[1]
    exchange_segment = header[2]
    security_id = header[3]

    body = raw[12:]
    packet_fmt = '<dII'
    packet_size = struct.calcsize(packet_fmt)
    depth = []
    
    for i in range(20):
        start = i * packet_size
        end = start + packet_size
        if end > len(body):
            break
        try:
            price, qty, orders = struct.unpack(packet_fmt, body[start:end])
        except struct.error:
            break
        depth.append({"price": float(price), "quantity": int(qty), "orders": int(orders)})
    
    if msg_code == 41:
        mtype = "Bid"
    elif msg_code == 51:
        mtype = "Ask"
    else:
        mtype = f"Other({msg_code})"

    return {
        "msg_length": msg_length,
        "msg_code": msg_code,
        "exchange_segment": exchange_segment,
        "security_id": security_id,
        "type": mtype,
        "depth": depth
    }

class DepthManager:
    def __init__(self, client_id: str, access_token: str, out_queue: queue.Queue, alert_engine: AlertEngine):
        self.client_id = client_id
        self.access_token = access_token
        self.out_queue = out_queue
        self.alert_engine = alert_engine
        self._instruments: List[Tuple[int, str]] = []
        self._loop: Optional[asyncio.AbstractEventLoop] = None
        self._thread: Optional[threading.Thread] = None
        self._stop_event = threading.Event()
        self.ws = None
        self.connected = False

    def start(self):
        if self._thread and self._thread.is_alive():
            return
        self._stop_event.clear()
        self._thread = threading.Thread(target=self._run_loop_thread, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop_event.set()
        if self._loop and self._loop.is_running():
            asyncio.run_coroutine_threadsafe(self._shutdown(), self._loop)

    async def _shutdown(self):
        try:
            if self.ws:
                await self.ws.close()
            await asyncio.sleep(0.1)
            self._loop.stop()
        except Exception:
            pass

    def _run_loop_thread(self):
        self._loop = asyncio.new_event_loop()
        asyncio.set_event_loop(self._loop)
        try:
            self._loop.run_until_complete(self._main())
        finally:
            tasks = asyncio.all_tasks(loop=self._loop)
            for t in tasks:
                t.cancel()
            try:
                self._loop.run_until_complete(self._loop.shutdown_asyncgens())
            except Exception:
                pass
            self._loop.close()

    async def _main(self):
        while not self._stop_event.is_set():
            try:
                url = f"{DEPTH_WSS}?token={self.access_token}&clientId={self.client_id}&authType=2"
                async with websockets.connect(url, max_size=None) as ws:
                    self.ws = ws
                    self.connected = True
                    if self._instruments:
                        await self._send_subscribe(self._instruments)
                    while not self._stop_event.is_set():
                        try:
                            raw = await asyncio.wait_for(ws.recv(), timeout=20)
                        except asyncio.TimeoutError:
                            try:
                                await ws.ping()
                            except Exception:
                                break
                            continue
                        if raw is None:
                            break
                        if isinstance(raw, str):
                            try:
                                j = json.loads(raw)
                                self.out_queue.put({"type": "text", "data": j})
                                continue
                            except Exception:
                                continue
                        if isinstance(raw, (bytes, bytearray)):
                            cursor = 0
                            while cursor < len(raw):
                                if cursor + 12 > len(raw):
                                    break
                                header_slice = raw[cursor:cursor+12]
                                parsed = parse_header_slice(header_slice)
                                if not parsed:
                                    break
                                msg_length = parsed[0]
                                if msg_length <= 0:
                                    break
                                end_idx = cursor + msg_length
                                if end_idx > len(raw):
                                    break
                                message_raw = raw[cursor:end_idx]
                                parsed_msg = parse_depth_message(message_raw)
                                if parsed_msg:
                                    self.out_queue.put(parsed_msg)
                                cursor = end_idx
            except Exception as e:
                self.out_queue.put({"type": "error", "data": str(e)})
                self.connected = False
                await asyncio.sleep(2)
        self.connected = False

    async def _send_subscribe(self, instruments: List[Tuple[int, str]]):
        if not self.ws:
            return
        exchange_map = {1: "NSE_EQ", 2: "NSE_FNO"}
        msg = {
            "RequestCode": DEPTH_20_REQ,
            "InstrumentCount": len(instruments),
            "InstrumentList": [
                {"ExchangeSegment": exchange_map.get(ex, str(ex)), "SecurityId": token}
                for ex, token in instruments
            ]
        }
        try:
            await self.ws.send(json.dumps(msg))
            self.out_queue.put({"type": "info", "data": f"Subscribed: {len(instruments)} instruments"})
        except Exception as e:
            self.out_queue.put({"type": "error", "data": f"Subscribe failed: {e}"})

    def subscribe(self, instruments: List[Tuple[int, str]]):
        existing = set(self._instruments)
        to_add = []
        for tup in instruments:
            if tup not in existing:
                existing.add(tup)
                to_add.append(tup)
        self._instruments = list(existing)
        if self._loop and self._loop.is_running() and to_add:
            asyncio.run_coroutine_threadsafe(self._send_subscribe(to_add), self._loop)

    def unsubscribe(self, instruments: List[Tuple[int, str]]):
        existing = set(self._instruments)
        for tup in instruments:
            existing.discard(tup)
        self._instruments = list(existing)
        self.out_queue.put({"type": "info", "data": f"Unsubscribed {len(instruments)} locally."})

# ==================== SESSION INITIALIZATION ====================

def init_session():
    """Initialize session state for both order flow and depth analysis"""
    # Order flow components
    if "stock_mapping" not in st.session_state:
        st.session_state["stock_mapping"] = load_stock_mapping()
    
    # Depth analysis components
    if "depth_manager" not in st.session_state:
        st.session_state["depth_queue"] = queue.Queue()
        st.session_state["alert_engine"] = AlertEngine()
        st.session_state["client_id"] = st.session_state.get("client_id", "1100244268")
        st.session_state["access_token"] = st.session_state.get("access_token", 
            "eyJ0eXAiOiJKV1QiLCJhbGciOiJIUzUxMiJ9.eyJpc3MiOiJkaGFuIiwicGFydG5lcklkIjoiIiwiZXhwIjoxNzU5MDM3OTE2LCJ0b2tlbkNvbnN1bWVyVHlwZSI6IlNFTEYiLCJ3ZWJob29rVXJsIjoiIiwiZGhhbkNsaWVudElkIjoiMTEwMDI0NDI2OCJ9.NiJopQOOMl9I3sFI4HUp-d4a-9HKpEXo5EL6jtJheLsjubkzC1saXOx1mjIh-H8_IXCgIXqAjAYydE-sNBnKHg")
        st.session_state["depth_manager"] = DepthManager(
            client_id=st.session_state["client_id"],
            access_token=st.session_state["access_token"],
            out_queue=st.session_state["depth_queue"],
            alert_engine=st.session_state["alert_engine"]
        )
        st.session_state["subscribed"] = []
        st.session_state["latest"] = {}
        st.session_state["recent_alerts"] = []

@st.cache_data
def load_stock_mapping():
    try:
        stock_df = pd.read_csv(STOCK_LIST_FILE)
        mapping = {str(k): v for k, v in zip(stock_df['security_id'], stock_df['symbol'])}
        return mapping
    except Exception as e:
        st.error(f"Failed to load stock list: {e}")
        return {}

# ==================== ORDER FLOW FUNCTIONS ====================

def send_telegram_alert(message):
    """Send message to Telegram"""
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        return False
    
    try:
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
        payload = {
            'chat_id': TELEGRAM_CHAT_ID,
            'text': message,
            'parse_mode': 'HTML'
        }
        response = requests.post(url, json=payload, timeout=10)
        return response.status_code == 200
    except Exception as e:
        st.error(f"Failed to send Telegram alert: {e}")
        return False

def fetch_live_data(security_id):
    """Fetch live data and update local cache"""
    api_url = f"{FLASK_API_BASE}/delta_data/{security_id}?interval=1"
    try:
        r = requests.get(api_url, timeout=20)
        r.raise_for_status()
        live_data = pd.DataFrame(r.json())
        if not live_data.empty:
            live_data['timestamp'] = pd.to_datetime(live_data['timestamp'])
            live_data.sort_values('timestamp', inplace=True)
            return live_data
    except Exception as e:
        st.warning(f"Live API fetch failed: {e}")
    return pd.DataFrame()

def aggregate_data(df, interval_minutes):
    df_copy = df.copy()
    df_copy.set_index('timestamp', inplace=True)
    df_agg = df_copy.resample(f"{interval_minutes}min").agg({
        'buy_initiated': 'sum',
        'sell_initiated': 'sum',
        'open': 'first',
        'high': 'max',
        'low': 'min',
        'close': 'last',
        'buy_volume': 'sum',
        'sell_volume': 'sum'
    }).dropna().reset_index()

    df_agg['tick_delta'] = df_agg['buy_initiated'] - df_agg['sell_initiated']
    df_agg['cumulative_tick_delta'] = df_agg['tick_delta'].cumsum()
    df_agg['inference'] = df_agg['tick_delta'].apply(
        lambda x: 'Buy Dominant' if x > 0 else ('Sell Dominant' if x < 0 else 'Neutral')
    )
    df_agg['delta'] = df_agg['buy_volume'] - df_agg['sell_volume']
    df_agg['cumulative_delta'] = df_agg['delta'].cumsum()
    
    return df_agg

# ==================== DEPTH ANALYSIS FUNCTIONS ====================

def consume_queue_and_update_latest(max_messages=200):
    """Process depth messages and generate alerts"""
    q: queue.Queue = st.session_state["depth_queue"]
    alert_engine: AlertEngine = st.session_state["alert_engine"]
    cnt = 0
    new_alerts = []
    
    while not q.empty() and cnt < max_messages:
        try:
            msg = q.get_nowait()
        except queue.Empty:
            break
        cnt += 1
        
        if msg.get("type") == "text":
            continue
        if msg.get("type") == "error":
            st.session_state.setdefault("_errors", []).append(msg["data"])
            continue
        if msg.get("type") in ("info",):
            st.session_state.setdefault("_infos", []).append(msg["data"])
            continue
            
        sec = str(msg["security_id"])
        meta = st.session_state["latest"].get(sec, {
            "bid": None, 
            "ask": None, 
            "exchange_segment": msg.get("exchange_segment")
        })
        
        if msg["type"] == "Bid":
            meta["bid"] = msg["depth"]
        elif msg["type"] == "Ask":
            meta["ask"] = msg["depth"]
        else:
            continue
            
        meta["last_ts"] = datetime.now().strftime("%H:%M:%S")
        st.session_state["latest"][sec] = meta
        
        # Run alert analysis if we have both bid and ask data
        if meta.get("bid") and meta.get("ask"):
            alerts = alert_engine.analyze_depth_and_generate_alerts(sec, meta["bid"], meta["ask"])
            new_alerts.extend(alerts)
    
    # Update recent alerts
    if new_alerts:
        st.session_state["recent_alerts"] = alert_engine.get_recent_alerts(50)

def build_combined_df_for_security(sec_id: str):
    """Combine up to 20-level bid and ask into a DataFrame"""
    from itertools import zip_longest
    
    rec = st.session_state["latest"].get(str(sec_id))
    if not rec:
        return pd.DataFrame()
    bids = rec.get("bid") or []
    asks = rec.get("ask") or []
    
    bids_sorted = sorted([b for b in bids if b["price"] > 0], key=lambda x: x["price"], reverse=True)
    asks_sorted = sorted([a for a in asks if a["price"] > 0], key=lambda x: x["price"])
    
    rows = []
    for b, a in zip_longest(bids_sorted, asks_sorted, fillvalue=None):
        row = {
            "bid_price": (b["price"] if b else None),
            "bid_qty": (b["quantity"] if b else None),
            "bid_orders": (b["orders"] if b else None),
            "ask_price": (a["price"] if a else None),
            "ask_qty": (a["quantity"] if a else None),
            "ask_orders": (a["orders"] if a else None),
        }
        rows.append(row)
    return pd.DataFrame(rows)

def create_depth_chart(sec_id: str):
    """Create interactive depth visualization"""
    rec = st.session_state["latest"].get(str(sec_id))
    if not rec or not rec.get("bid") or not rec.get("ask"):
        return None
        
    bids = sorted([b for b in rec["bid"] if b["price"] > 0], key=lambda x: x["price"], reverse=True)
    asks = sorted([a for a in rec["ask"] if a["price"] > 0], key=lambda x: x["price"])
    
    fig = make_subplots(specs=[[{"secondary_y": False}]])
    
    # Bid side (green)
    bid_prices = [b["price"] for b in bids]
    bid_qtys = [b["quantity"] for b in bids]
    bid_cumulative = np.cumsum(bid_qtys)
    
    fig.add_trace(
        go.Scatter(
            x=bid_prices, 
            y=bid_cumulative,
            mode='lines+markers',
            name='Bid Depth',
            line=dict(color='green', width=2),
            fill='tozeroy',
            fillcolor='rgba(0,255,0,0.1)'
        )
    )
    
    # Ask side (red)
    ask_prices = [a["price"] for a in asks]
    ask_qtys = [a["quantity"] for a in asks]
    ask_cumulative = np.cumsum(ask_qtys)
    
    fig.add_trace(
        go.Scatter(
            x=ask_prices, 
            y=ask_cumulative,
            mode='lines+markers',
            name='Ask Depth',
            line=dict(color='red', width=2),
            fill='tozeroy',
            fillcolor='rgba(255,0,0,0.1)'
        )
    )
    
    fig.update_layout(
        title=f"Market Depth - {sec_id}",
        xaxis_title="Price",
        yaxis_title="Cumulative Quantity",
        height=400
    )
    
    return fig

# ==================== UI COMPONENTS ====================

def render_order_flow_tab():
    """Render the order flow analysis tab"""
    st.header("Order Flow Analysis")
    
    # Security selection
    @st.cache_data(ttl=6000)
    def fetch_security_ids():
        try:
            stock_df = pd.read_csv(STOCK_LIST_FILE)
            ids = sorted(list(stock_df['security_id'].unique()))
            stock_mapping = st.session_state["stock_mapping"]
            return [f"{stock_mapping.get(str(i), f'Stock {i}')} ({i})" for i in ids]
        except Exception as e:
            st.error(f"Failed to fetch security IDs: {e}")
            return ["No Data Available (0)"]

    security_options = fetch_security_ids()
    selected_option = st.selectbox("Select Security", security_options)
    
    # Extract security ID
    match = re.search(r'\((\d+)\)', selected_option)
    if match:
        selected_id = int(match.group(1))
        if selected_id == 0:
            st.error("No security data available. Please check your data source.")
            return
    else:
        st.error(f"Selected option '{selected_option}' does not contain a valid ID")
        return

    # Interval selection
    interval = st.selectbox("Interval (minutes)", [1, 3, 5, 15, 30, 60], index=2)
    
    # Fetch and process data
    with st.spinner("Fetching order flow data..."):
        live_df = fetch_live_data(selected_id)
        
        if live_df.empty:
            st.warning("No order flow data available for this security.")
            return
        
        # Filter for current day
        today = datetime.now().date()
        start_time = datetime.combine(today, datetime.time(9, 0))
        end_time   = datetime.combine(today, datetime.time(23, 59, 59))

        live_df = live_df[(live_df['timestamp'] >= pd.Timestamp(start_time)) & 
                         (live_df['timestamp'] <= pd.Timestamp(end_time))]
        
        agg_df = aggregate_data(live_df, interval)
    
    if not agg_df.empty:
        # Display metrics
        latest = agg_df.iloc[-1]
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            st.metric("Current Price", f"₹{latest['close']:.2f}")
        with col2:
            st.metric("Tick Delta", f"{int(latest['tick_delta'])}")
        with col3:
            st.metric("Cumulative Tick Delta", f"{int(latest['cumulative_tick_delta'])}")
        with col4:
            st.metric("Total Volume", f"{int(latest['buy_initiated'] + latest['sell_initiated']):,}")
        
        # Create order flow chart
        fig = go.Figure()
        
        # Add candlestick chart
        fig.add_trace(go.Candlestick(
            x=agg_df['timestamp'],
            open=agg_df['open'],
            high=agg_df['high'],
            low=agg_df['low'],
            close=agg_df['close'],
            name="Price"
        ))
        
        fig.update_layout(
            title=f"Order Flow Chart - {selected_option}",
            xaxis_title="Time",
            yaxis_title="Price",
            height=500
        )
        
        st.plotly_chart(fig, use_container_width=True)
        
        # Show data table
        st.subheader("Order Flow Data")
        columns_to_show = ['timestamp', 'close', 'buy_initiated', 'sell_initiated', 
                          'tick_delta', 'cumulative_tick_delta', 'inference']
        display_df = agg_df[columns_to_show].copy()
        display_df['timestamp'] = display_df['timestamp'].dt.strftime('%H:%M:%S')
        
        st.dataframe(display_df, use_container_width=True, height=400)
        
        # Download option
        csv = agg_df.to_csv(index=False).encode('utf-8')
        st.download_button(
            "Download Order Flow Data", 
            csv, 
            f"orderflow_{selected_id}_{datetime.now().strftime('%Y%m%d_%H%M')}.csv", 
            "text/csv"
        )
    else:
        st.warning("No processed data available for the selected timeframe.")

def render_depth_tab():
    """Render the market depth analysis tab"""
    st.header("Market Depth Analysis")
    
    # Connection controls
    col1, col2 = st.columns([1, 2])
    
    with col1:
        st.subheader("Connection")
        start_btn = st.button("Start Depth Feed", type="primary")
        stop_btn = st.button("Stop Depth Feed")
        
        connected = st.session_state["depth_manager"].connected
        status_color = "🟢" if connected else "🔴"
        st.write(f"Status: {status_color} {'Connected' if connected else 'Disconnected'}")
        
        if start_btn:
            st.session_state["depth_manager"].start()
            st.success("Depth manager started.")
            time.sleep(1)
            st.rerun()
            
        if stop_btn:
            st.session_state["depth_manager"].stop()
            st.success("Depth manager stopped.")
            time.sleep(1)
            st.rerun()
    
    with col2:
        st.subheader("Add Subscription")
        st.caption("Exchange codes: 1 = NSE_EQ, 2 = NSE_FNO")
        
        col2a, col2b, col2c = st.columns([1, 2, 1])
        with col2a:
            ex = st.number_input("Exchange", min_value=1, max_value=99, step=1, value=2)
        with col2b:
            sec_id = st.text_input("Security ID", value="", placeholder="e.g., 26009 for Nifty")
        with col2c:
            add_btn = st.button("Add")
        
        if add_btn and sec_id.strip():
            tup = (int(ex), str(sec_id.strip()))
            st.session_state["subscribed"].append(tup)
            st.session_state["subscribed"] = list(dict.fromkeys(st.session_state["subscribed"]))
            st.session_state["depth_manager"].subscribe([tup])
            st.success(f"Subscribed to ({ex}, {sec_id.strip()})")
            time.sleep(1)
            st.rerun()
    
    # Current subscriptions
    st.subheader("Current Subscriptions")
    if st.session_state["subscribed"]:
        for i, tup in enumerate(st.session_state["subscribed"]):
            col1, col2, col3 = st.columns([2, 2, 1])
            with col1:
                st.write(f"Exchange: {tup[0]}")
            with col2:
                st.write(f"Security ID: {tup[1]}")
            with col3:
                if st.button("Remove", key=f"unsub_{i}"):
                    st.session_state["subscribed"].remove(tup)
                    st.session_state["depth_manager"].unsubscribe([tup])
                    st.rerun()
    else:
        st.info("No active subscriptions")
    
    # Process incoming messages
    consume_queue_and_update_latest()
    
    # Display depth data for subscribed securities
    if st.session_state["subscribed"]:
        st.subheader("Live Market Depth")
        
        # Create tabs for each subscribed security
        if len(st.session_state["subscribed"]) > 1:
            tabs = st.tabs([f"Security {tup[1]}" for tup in st.session_state["subscribed"]])
            
            for idx, tup in enumerate(st.session_state["subscribed"]):
                with tabs[idx]:
                    render_security_depth(tup[1])
        else:
            render_security_depth(st.session_state["subscribed"][0][1])
    else:
        st.info("Subscribe to at least one instrument to view market depth")

def render_security_depth(sec_id: str):
    """Render depth analysis for a specific security"""
    meta = st.session_state["latest"].get(str(sec_id))
    
    if not meta:
        st.warning("Waiting for data...")
        return
        
    if not (meta.get("bid") and meta.get("ask")):
        st.warning("Waiting for complete bid/ask data...")
        return
    
    # Key metrics
    best_bid = max(meta["bid"], key=lambda x: x["price"]) if meta["bid"] else None
    best_ask = min(meta["ask"], key=lambda x: x["price"]) if meta["ask"] else None
    
    if best_bid and best_ask:
        spread = best_ask["price"] - best_bid["price"]
        mid_price = (best_bid["price"] + best_ask["price"]) / 2
        spread_pct = (spread / mid_price) * 100 if mid_price > 0 else 0
        
        col1, col2, col3, col4 = st.columns(4)
        col1.metric("Best Bid", f"₹{best_bid['price']:.2f}", f"{best_bid['quantity']} qty")
        col2.metric("Best Ask", f"₹{best_ask['price']:.2f}", f"{best_ask['quantity']} qty")
        col3.metric("Spread", f"₹{spread:.2f}", f"{spread_pct:.3f}%")
        col4.metric("Mid Price", f"₹{mid_price:.2f}")
    
    # Recent alerts for this security
    security_alerts = st.session_state["alert_engine"].get_alerts_for_security(str(sec_id), 3)
    if security_alerts:
        st.subheader("Recent Alerts")
        for alert in security_alerts:
            alert_color = "error" if alert.get('severity') == 'HIGH' else "warning"
            getattr(st, alert_color)(f"{alert['type'].replace('_', ' ').title()}: {alert['message']}")
    
    # Depth visualization and data
    col1, col2 = st.columns([1, 1])
    
    with col1:
        st.subheader("Depth Chart")
        chart = create_depth_chart(sec_id)
        if chart:
            st.plotly_chart(chart, use_container_width=True)
        else:
            st.info("Chart will appear once data is available")
    
    with col2:
        st.subheader("Market Depth Table")
        df = build_combined_df_for_security(sec_id)
        if not df.empty:
            st.dataframe(df.head(10), use_container_width=True, hide_index=True)
    
    st.caption(f"Last updated: {meta.get('last_ts', 'Never')}")

def render_alerts_tab():
    """Render the alerts and monitoring tab"""
    st.header("Smart Alerts & Monitoring")
    
    # Alert configuration
    with st.expander("Alert Settings"):
        col1, col2 = st.columns(2)
        with col1:
            st.number_input("Large Order Threshold", 
                          value=ALERT_CONFIG['large_order_threshold'], 
                          key="large_order_threshold")
            st.number_input("Imbalance Ratio Threshold", 
                          value=ALERT_CONFIG['imbalance_ratio_threshold'], 
                          key="imbalance_ratio_threshold")
        with col2:
            st.number_input("Volume Spike Threshold", 
                          value=ALERT_CONFIG['volume_spike_threshold'], 
                          key="volume_spike_threshold")
            st.number_input("Spread Compression %", 
                          value=ALERT_CONFIG['spread_compression_threshold'], 
                          key="spread_compression_threshold")
    
    # Telegram alerts
    st.subheader("Telegram Alerts")
    col1, col2 = st.columns(2)
    with col1:
        if st.button("Test Telegram Connection"):
            test_message = "🧪 Test alert from ComOflo Dashboard"
            if send_telegram_alert(test_message):
                st.success("Telegram test successful!")
            else:
                st.error("Telegram test failed. Check configuration.")
    
    with col2:
        if st.button("Send Zero Cross Test"):
            test_message = f"""
🔄 <b>ZERO CROSS TEST ALERT</b>

📈 <b>Stock:</b> TEST STOCK
⚡ <b>Event:</b> CROSSED ABOVE ZERO
📊 <b>Cumulative Tick Delta:</b> +75
⏰ <b>Time:</b> {datetime.now().strftime('%H:%M:%S')}

This is a test of the zero cross alert system!
            """.strip()
            
            if send_telegram_alert(test_message):
                st.success("Zero cross test alert sent!")
            else:
                st.error("Failed to send zero cross test alert")
    
    # Recent alerts display
    st.subheader("Recent Depth Alerts")
    recent_alerts = st.session_state.get("recent_alerts", [])
    
    if recent_alerts:
        for i, alert in enumerate(recent_alerts[:10]):
            severity_indicator = "🔴" if alert.get('severity') == 'HIGH' else "🟡"
            timestamp_str = alert['timestamp'].strftime("%H:%M:%S")
            
            alert_type = alert['type'].replace('_', ' ').title()
            
            with st.container():
                if alert.get('severity') == 'HIGH':
                    st.error(f"{severity_indicator} **{alert_type}** - {alert['security_id']} at {timestamp_str}")
                else:
                    st.warning(f"{severity_indicator} **{alert_type}** - {alert['security_id']} at {timestamp_str}")
                
                st.caption(alert['message'])
                st.divider()
    else:
        st.info("No alerts yet. Start the depth feed and subscribe to instruments to receive alerts.")

# ==================== MAIN APPLICATION ====================

def main():
    """Main application entry point"""
    init_session()
    
    st.title("ComOflo + Depth Dashboard")
    st.markdown("**Integrated Order Flow & Market Depth Analysis Platform**")
    
    # Main navigation
    tab1, tab2, tab3, tab4 = st.tabs(["📊 Order Flow", "📈 Market Depth", "🚨 Alerts", "⚙️ Settings"])
    
    with tab1:
        render_order_flow_tab()
    
    with tab2:
        render_depth_tab()
    
    with tab3:
        render_alerts_tab()
    
    with tab4:
        st.header("Settings & Configuration")
        
        st.subheader("Depth Feed Credentials")
        col1, col2 = st.columns(2)
        with col1:
            client_id = st.text_input("Client ID", value=st.session_state.get("client_id", ""))
        with col2:
            access_token = st.text_area("Access Token", value=st.session_state.get("access_token", ""), height=100)
        
        if st.button("Update Credentials"):
            st.session_state["client_id"] = client_id
            st.session_state["access_token"] = access_token
            # Recreate depth manager with new credentials
            st.session_state["depth_manager"] = DepthManager(
                client_id=client_id,
                access_token=access_token,
                out_queue=st.session_state["depth_queue"],
                alert_engine=st.session_state["alert_engine"]
            )
            st.success("Credentials updated!")
        
        st.subheader("Telegram Configuration")
        st.info("Configure Telegram credentials in Streamlit secrets to enable alerts")
        
        st.subheader("Data Sources")
        st.info(f"Order Flow API: {FLASK_API_BASE}")
        st.info(f"Depth WebSocket: {DEPTH_WSS}")

if __name__ == "__main__":

    main()


