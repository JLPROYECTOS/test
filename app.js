(()=>{'use strict';
const VERSION='1.1.0';
const $=(s,r=document)=>r.querySelector(s);
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const fmt=(n,d=1)=>Number.isFinite(n)?+n.toFixed(d):n;
const errMsg=e=>e&&e.name?e.name+(e.message?': '+e.message:''):String(e);
const withTimeout=(p,ms,label='Tiempo agotado')=>{let t;return Promise.race([p,new Promise((_,rej)=>t=setTimeout(()=>rej(new Error(label)),ms))]).finally(()=>clearTimeout(t));};
const stopStream=s=>{try{s&&s.getTracks().forEach(t=>t.stop())}catch{}};
const median=a=>{if(!a.length)return null;const s=[...a].sort((x,y)=>x-y),m=s.length>>1;return s.length%2?s[m]:(s[m-1]+s[m])/2;};
const db=x=>fmt(20*Math.log10(Math.max(x,1e-6)),1);
const ST={ok:{label:'OK',icon:'✅'},fail:{label:'Fallo',icon:'❌'},unsupported:{label:'No soportado',icon:'🚫'},manual:{label:'Manual',icon:'✋'},pending:{label:'Pendiente',icon:'⏳'}};
const R=(status,note='',data={})=>({status,note,data});
const vs=v=>v==='ok'?'ok':v==='fail'?'fail':null;
const results={};
const AC=window.AudioContext||window.webkitAudioContext;
const hasGUM=()=>!!(navigator.mediaDevices&&navigator.mediaDevices.getUserMedia);
function gumErr(e){const m={NotAllowedError:'Permiso denegado (usuario o navegador)',NotFoundError:'Dispositivo no encontrado',NotReadableError:'Dispositivo en uso por otra app o bloqueado por el sistema',OverconstrainedError:'Configuración no soportada por el dispositivo',SecurityError:'Requiere HTTPS / contexto seguro',AbortError:'Acceso abortado'};return m[e&&e.name]||errMsg(e);}

/* ---------- Sensores ---------- */
class SensorMonitor{
  constructor(){this._m=e=>this.motion(e);this._o=e=>this.orient(e,false);this._oa=e=>this.orient(e,true);this.reset();}
  reset(){this.n={motion:0,accel:0,gyro:0,orient:0};this.last={};this.rng={};this.t0=performance.now();this.a0=null;this.hasAbs=false;}
  start(){this.reset();addEventListener('devicemotion',this._m);addEventListener('deviceorientation',this._o);addEventListener('deviceorientationabsolute',this._oa);}
  stop(){removeEventListener('devicemotion',this._m);removeEventListener('deviceorientation',this._o);removeEventListener('deviceorientationabsolute',this._oa);}
  track(k,v){if(v==null||!Number.isFinite(v))return;const r=this.rng[k]||(this.rng[k]={min:v,max:v});r.min=Math.min(r.min,v);r.max=Math.max(r.max,v);}
  motion(e){this.n.motion++;const a=e.accelerationIncludingGravity;
    if(a&&a.x!=null){this.n.accel++;this.last.accel=a;['x','y','z'].forEach(k=>this.track('a'+k,a[k]));}
    const g=e.rotationRate;
    if(g&&g.alpha!=null){this.n.gyro++;this.last.gyro=g;['alpha','beta','gamma'].forEach(k=>this.track('g'+k,g[k]));}}
  orient(e,abs){if(e.alpha==null&&e.beta==null&&e.gamma==null)return;
    if(abs){this.hasAbs=true;if(e.alpha!=null)this.last.heading=(360-e.alpha)%360;return;}
    this.n.orient++;this.last.orient=e;this.track('ob',e.beta);this.track('og',e.gamma);
    if(e.alpha!=null){if(this.a0==null)this.a0=e.alpha;this.track('od',((e.alpha-this.a0+540)%360)-180);
      if(!this.hasAbs)this.last.heading=e.webkitCompassHeading!=null?e.webkitCompassHeading:(360-e.alpha)%360;}}
  range(k){const x=this.rng[k];return x?x.max-x.min:0;}
  changed(th){const r=k=>this.range(k);return{accel:Math.max(r('ax'),r('ay'),r('az'))>th.a,gyro:Math.max(r('galpha'),r('gbeta'),r('ggamma'))>th.g,orient:Math.max(r('ob'),r('og'),r('od'))>th.o};}
}
const TH_AUTO={a:.35,g:4,o:4},TH_GUIDED={a:1.5,g:25,o:15};
const xyz=(o,k=['x','y','z'])=>o?k.map(c=>c+' '+fmt(o[c],2)).join(' · '):'—';
function evalSensors(m,th){
  const sec=(performance.now()-m.t0)/1000||1,rg=k=>fmt(m.range(k),2);
  const data={
    frecuenciaMovimientoHz:Math.round(m.n.motion/sec),frecuenciaOrientacionHz:Math.round(m.n.orient/sec),
    acelerometro:'eventos '+m.n.accel+' · último '+xyz(m.last.accel)+' m/s² · rango '+[rg('ax'),rg('ay'),rg('az')].join('/'),
    giroscopio:'eventos '+m.n.gyro+' · último '+xyz(m.last.gyro,['alpha','beta','gamma'])+' °/s · rango máx '+Math.max(rg('galpha'),rg('gbeta'),rg('ggamma')),
    orientacion:'eventos '+m.n.orient+' · '+(m.last.orient?'α '+fmt(m.last.orient.alpha,0)+' β '+fmt(m.last.orient.beta,0)+' γ '+fmt(m.last.orient.gamma,0):'—')+' · rango β/γ '+rg('ob')+'/'+rg('og'),
    brujula:(m.hasAbs?'absoluta (norte magnético)':'relativa (sin norte real)')+' · rumbo '+(m.last.heading!=null?Math.round(m.last.heading)+'°':'—')};
  const miss=[];if(!m.n.accel)miss.push('acelerómetro');if(!m.n.gyro)miss.push('giroscopio');if(!m.n.orient)miss.push('orientación');
  if(miss.length===3)return R('fail','Sin eventos de sensores (¿permiso "Sensores de movimiento" bloqueado para el sitio?)',data);
  if(miss.length)return R('fail','Sin datos de: '+miss.join(', ')+' (ausente o averiado)',data);
  const ch=m.changed(th),nc=[];if(!ch.accel)nc.push('acelerómetro');if(!ch.gyro)nc.push('giroscopio');if(!ch.orient)nc.push('orientación');
  data.movimientoDetectado=Object.entries(ch).map(([k,v])=>k+':'+(v?'sí':'no')).join(' ');
  return nc.length?R('manual','Sensores activos pero sin cambio detectado en: '+nc.join(', ')+'. Mueve el teléfono (test guiado).',data):R('ok','',data);
}

/* ---------- Pruebas automáticas ---------- */
async function envAuto(){
  const n=navigator,ua=n.userAgent,u=n.userAgentData;let hi={};
  try{if(u&&u.getHighEntropyValues)hi=await withTimeout(u.getHighEntropyValues(['model','platformVersion']),1500);}catch{}
  const data={userAgent:ua,plataforma:(u&&u.platform)||n.platform||'?',modelo:hi.model||'(no expuesto)',versionSO:hi.platformVersion||'?',
    movil:u?u.mobile:/Mobi|Android/i.test(ua),navegador:u&&u.brands?u.brands.map(b=>b.brand+' '+b.version).join(', '):'?',
    idioma:n.language,zonaHoraria:Intl.DateTimeFormat().resolvedOptions().timeZone,nucleosCPU:n.hardwareConcurrency||'?',
    memoriaGB_aprox:n.deviceMemory||'(no expuesto)',contextoSeguro:isSecureContext,maxTouchPoints:n.maxTouchPoints,online:n.onLine,
    instaladaComoApp:matchMedia('(display-mode: standalone)').matches};
  if(!isSecureContext)return R('fail','Contexto no seguro: abre la página por HTTPS (GitHub Pages) o muchas APIs fallarán.',data);
  return R('ok',/Android/i.test(ua)?'':'No parece Android: algunos resultados pueden diferir.',data);
}
async function capsAuto(){
  const o={},issues=[];let sup=0;
  try{const c=document.createElement('canvas'),gl=c.getContext('webgl2')||c.getContext('webgl');
    if(gl){const x=gl.getExtension('WEBGL_debug_renderer_info');o.webgl=(window.WebGL2RenderingContext&&gl instanceof WebGL2RenderingContext?'WebGL2':'WebGL1')+' · GPU '+(x?gl.getParameter(x.UNMASKED_RENDERER_WEBGL):'(oculta)')+' · textura máx '+gl.getParameter(gl.MAX_TEXTURE_SIZE);sup++;}else o.webgl='no soportado';}
  catch(e){o.webgl='error: '+errMsg(e);issues.push('WebGL');}
  if(window.RTCPeerConnection){try{const pc=new RTCPeerConnection();pc.createDataChannel('t');const of=await withTimeout(pc.createOffer(),3000);pc.close();o.webrtc=of&&of.sdp?'OK (oferta SDP generada)':'sin SDP';sup++;}catch(e){o.webrtc='error: '+errMsg(e);issues.push('WebRTC');}}else o.webrtc='no soportado';
  if('wakeLock' in navigator){try{const l=await navigator.wakeLock.request('screen');await l.release();o.wakeLock='OK (adquirido y liberado)';sup++;}catch(e){o.wakeLock='error: '+errMsg(e);issues.push('Wake Lock');}}else o.wakeLock='no soportado';
  const cb=navigator.clipboard;o.portapapeles=cb&&cb.writeText?'API disponible':'no soportado';if(cb&&cb.writeText)sup++;
  const y=k=>k?'sí':'no';
  o.otras='WebAudio '+y(AC)+' · MediaRecorder '+y(window.MediaRecorder)+' · ServiceWorker '+y('serviceWorker' in navigator)+' · WebShare '+y(navigator.share)+' · Bluetooth '+y(navigator.bluetooth)+' · NFC '+y(window.NDEFReader)+' · USB '+y(navigator.usb)+' · Generic Sensors '+y(window.Accelerometer)+' · Notificaciones '+y(window.Notification);
  if(!sup)return R('unsupported','Ninguna de las capacidades principales está disponible',o);
  if(issues.length)return R('fail','Fallan: '+issues.join(', '),o);
  return R('ok','',o);
}
async function screenAuto(){
  const s=screen,d=devicePixelRatio;
  const hz=await withTimeout(new Promise(res=>{let t0=null,f=0;const tick=t=>{if(t0==null)t0=t;else f++;if(t-t0<600)requestAnimationFrame(tick);else res(f*1000/(t-t0));};requestAnimationFrame(tick);}),2000).catch(()=>null);
  const o=s.orientation;
  return R('ok','La resolución física es una estimación (CSS px × devicePixelRatio).',{resolucionCSS:s.width+'×'+s.height,resolucionFisicaAprox:Math.round(s.width*d)+'×'+Math.round(s.height*d),devicePixelRatio:fmt(d,2),viewport:innerWidth+'×'+innerHeight,
    orientacion:o?o.type+' '+o.angle+'°':(innerWidth>innerHeight?'horizontal':'vertical'),profundidadColor:s.colorDepth+' bits',gamaP3:matchMedia('(color-gamut: p3)').matches,HDR:matchMedia('(dynamic-range: high)').matches,
    refrescoAproxHz:hz?Math.round(hz):'(n/d)',temaOscuroSistema:matchMedia('(prefers-color-scheme: dark)').matches});
}
async function touchAuto(){
  const mp=navigator.maxTouchPoints||0;
  if(!mp&&!('ontouchstart' in window))return R('unsupported','Sin pantalla táctil detectada');
  return R('manual','Puntos táctiles declarados: '+mp+'. Verifica el multitouch real en el test guiado.',{maxTouchPointsDeclarado:mp});
}
async function sensorsAuto(){
  if(!('DeviceMotionEvent' in window)&&!('DeviceOrientationEvent' in window))return R('unsupported','API DeviceMotion/Orientation no disponible');
  const m=new SensorMonitor();m.start();await sleep(1800);m.stop();
  if(!m.n.motion&&!m.n.orient&&typeof DeviceMotionEvent!=='undefined'&&typeof DeviceMotionEvent.requestPermission==='function')return R('manual','Requiere permiso con gesto táctil; usa el test guiado.');
  return evalSensors(m,TH_AUTO);
}
async function netAuto(){
  const c=navigator.connection||navigator.mozConnection||navigator.webkitConnection,d={online:navigator.onLine};
  if(c){d.tipoRed=c.type||'(n/d)';d.effectiveType=c.effectiveType;d.downlinkMbps=c.downlink;d.rttMs=c.rtt;d.ahorroDatos=c.saveData;}else d.networkInformation='no disponible en este navegador';
  if(!navigator.onLine)return R('fail','Sin conexión (offline)',d);
  const own=[],ext=[],base=location.href.split('#')[0].split('?')[0];
  for(let i=0;i<4;i++){const t=performance.now();try{await withTimeout(fetch(base+'?_='+Date.now()+i,{method:'HEAD',cache:'no-store'}),5000);own.push(performance.now()-t);}catch{}}
  for(let i=0;i<3;i++){const t=performance.now();try{await withTimeout(fetch('https://www.gstatic.com/generate_204?_='+Date.now()+i,{mode:'no-cors',cache:'no-store'}),5000);ext.push(performance.now()-t);}catch{}}
  const sm=a=>a.length?{medianaMs:Math.round(median(a)),minMs:Math.round(Math.min(...a)),maxMs:Math.round(Math.max(...a)),muestras:a.length}:'sin respuesta';
  d.latenciaDominioPropio=sm(own);d.latenciaGstatic=sm(ext);
  try{const ac=new AbortController(),to=setTimeout(()=>ac.abort(),7000),t=performance.now();
    const r=await fetch('https://cdn.jsdelivr.net/npm/jquery@3.7.1/dist/jquery.min.js?_='+Date.now(),{cache:'no-store',signal:ac.signal});
    const b=await r.arrayBuffer();clearTimeout(to);const s=(performance.now()-t)/1000;
    d.descargaLigera={bytes:b.byteLength,segundos:fmt(s,2),Mbps_aprox:fmt(b.byteLength*8/s/1e6,2)};}catch(e){d.descargaLigera='no medida: '+errMsg(e);}
  if(!own.length&&!ext.length)return R('fail','No se pudo contactar ninguna URL (¿sin Internet real o bloqueo?)',d);
  const med=median(ext.length?ext:own);
  return R('ok',med>500?'Latencia alta (>500 ms)':'',d);
}
async function batteryAuto(){
  if(!navigator.getBattery)return R('unsupported','Battery API no disponible (solo Chrome/Android la ofrece)');
  const b=await navigator.getBattery(),t=x=>x===Infinity?'∞':x;
  return R('ok','Salud y ciclos no son accesibles desde el navegador: introdúcelos a mano en el test guiado.',{nivel:Math.round(b.level*100)+'%',cargando:b.charging,segundosHastaCarga:t(b.chargingTime),segundosHastaDescarga:t(b.dischargingTime),saludBateria:'no accesible desde el navegador',ciclosCarga:'no accesibles desde el navegador'});
}
function geoAuto(){return new Promise(res=>{
  if(!navigator.geolocation)return res(R('unsupported','Geolocation API no disponible'));
  const t0=performance.now();
  navigator.geolocation.getCurrentPosition(p=>{const c=p.coords;
    res(R('ok',c.accuracy>100?'Precisión baja (>100 m): probablemente ubicación por red/Wi-Fi o interior.':'',{latitud:+c.latitude.toFixed(6),longitud:+c.longitude.toFixed(6),precisionM:Math.round(c.accuracy),altitudM:c.altitude,velocidadMs:c.speed,rumbo:c.heading,tiempoRespuestaMs:Math.round(performance.now()-t0)}));},
  e=>res(R('fail',({1:'Permiso denegado',2:'Posición no disponible (¿ubicación del sistema desactivada?)',3:'Tiempo agotado sin fix'})[e.code]||'Error de geolocalización',{codigoError:e.code,tiempoMs:Math.round(performance.now()-t0)})),
  {enableHighAccuracy:true,timeout:15000,maximumAge:0});});}

/* ---------- Audio / mic / cámara / vibración ---------- */
async function audioAuto(){
  if(!AC)return R('unsupported','Web Audio API no disponible');
  const c=new AC();const d={estadoContexto:c.state,sampleRateHz:c.sampleRate,latenciaBaseS:fmt(c.baseLatency,4),canalesMaxSalida:c.destination.maxChannelCount,stereoPanner:typeof c.createStereoPanner==='function'};
  try{await c.close();}catch{}
  return R('manual','Motor de audio disponible. Confirma el sonido (altavoz, canales L/R) en el test guiado.',d);
}
async function audioGuided(ui){
  if(!AC)return R('unsupported','Web Audio API no disponible');
  const c=new AC();ui.onCleanup(()=>c.close().catch(()=>{}));
  ui.body.innerHTML='<p>Sube el volumen multimedia. Pulsa cada botón: deberías oír el tono solo por el lado indicado.</p><div class="grid2"><button class="btn" data-ch="L">🔈 Izquierdo</button><button class="btn" data-ch="R">Derecho 🔈</button><button class="btn" data-ch="C">🔊 Ambos</button><button class="btn" data-ch="S">〰 Barrido</button></div><p class="muted" id="aInfo">Si no oyes nada o falla un canal → Fallo. (Muchos móviles tienen un solo altavoz: en ese caso L/R suena igual.)</p>';
  const played=new Set();
  ui.body.addEventListener('click',async e=>{
    const b=e.target.closest('[data-ch]');if(!b)return;const ch=b.dataset.ch;played.add(ch);
    try{await c.resume();const t=c.currentTime,o=c.createOscillator(),g=c.createGain(),dur=ch==='S'?1.6:1;
      o.frequency.value=ch==='L'?440:ch==='R'?660:523;
      if(ch==='S'){o.frequency.setValueAtTime(200,t);o.frequency.exponentialRampToValueAtTime(2000,t+dur);}
      g.gain.setValueAtTime(0,t);g.gain.linearRampToValueAtTime(.25,t+.03);g.gain.linearRampToValueAtTime(0,t+dur);
      o.connect(g);
      if(c.createStereoPanner){const p=c.createStereoPanner();p.pan.value=ch==='L'?-1:ch==='R'?1:0;g.connect(p);p.connect(c.destination);}else g.connect(c.destination);
      o.start(t);o.stop(t+dur+.05);}catch(er){$('#aInfo').textContent='Error: '+errMsg(er);}
  });
  const v=await ui.verdict();
  return R(vs(v),v==='ok'&&played.size<3?'Marcado OK sin probar todos los canales':'',{botonesProbados:[...played].join(','),sampleRateHz:c.sampleRate,estado:c.state});
}
function levelMeter(stream,cb){
  const c=new AC(),src=c.createMediaStreamSource(stream),an=c.createAnalyser();an.fftSize=1024;src.connect(an);
  const buf=new Float32Array(an.fftSize);c.resume().catch(()=>{});
  const iv=setInterval(()=>{an.getFloatTimeDomainData(buf);let s=0;for(const v of buf)s+=v*v;cb(Math.sqrt(s/buf.length));},50);
  return{stop(){clearInterval(iv);try{src.disconnect()}catch{}c.close().catch(()=>{});}};
}
const openMic=()=>navigator.mediaDevices.getUserMedia({audio:{echoCancellation:false,noiseSuppression:false,autoGainControl:false}});
async function micAuto(){
  if(!hasGUM())return R('unsupported','getUserMedia no disponible (¿falta HTTPS?)');
  if(!AC)return R('unsupported','Web Audio API no disponible');
  let st;try{st=await openMic();}catch(e){return R('fail',gumErr(e));}
  try{const t=st.getAudioTracks()[0];let peak=0,sum=0,n=0;
    const m=levelMeter(st,r=>{peak=Math.max(peak,r);sum+=r;n++;});await sleep(1500);m.stop();
    const s=t.getSettings(),d={dispositivo:t.label||'(sin etiqueta)',estadoPista:t.readyState,silenciada:t.muted,sampleRateHz:s.sampleRate,canales:s.channelCount,nivelPicoDb:db(peak),nivelMedioDb:db(sum/Math.max(n,1))};
    if(t.readyState!=='live')return R('fail','La pista de audio no está activa',d);
    if(peak<1e-5)return R('manual','Señal totalmente plana; confirma en el test guiado hablando o soplando.',d);
    return R('ok','',d);
  }finally{stopStream(st);}
}
async function micGuided(ui){
  if(!hasGUM())return R('unsupported','getUserMedia no disponible (¿falta HTTPS?)');
  if(!AC)return R('unsupported','Web Audio API no disponible');
  let st;try{st=await openMic();}catch(e){return R('fail',gumErr(e));}
  ui.onCleanup(()=>stopStream(st));
  ui.body.innerHTML='<p id="mMsg">Habla o sopla cerca del micrófono…</p><div class="meter"><i id="mFill"></i></div><div class="muted" id="mDb"></div><button class="btn" id="rec" style="width:100%;margin-top:10px">⏺ Grabar 3 s y reproducir</button><audio id="player" controls hidden style="width:100%;margin-top:10px"></audio>';
  let peak=0,hits=0;
  const m=levelMeter(st,r=>{peak=Math.max(peak,r);const d=db(r);$('#mFill').style.width=Math.max(0,Math.min(100,(d+70)/70*100))+'%';$('#mDb').textContent=d+' dBFS · pico '+db(peak)+' dBFS';
    if(r>.02&&++hits===6){$('#mMsg').textContent='✓ Sonido detectado. Pulsa OK.';ui.suggest(true);}});
  ui.onCleanup(()=>m.stop());
  const rec=$('#rec');
  if(!window.MediaRecorder)rec.hidden=true;
  rec.onclick=()=>{try{const mr=new MediaRecorder(st),ch=[];mr.ondataavailable=e=>ch.push(e.data);
    mr.onstop=()=>{const a=$('#player');if(!a)return;a.src=URL.createObjectURL(new Blob(ch,{type:mr.mimeType}));a.hidden=false;a.play().catch(()=>{});rec.textContent='⏺ Grabar de nuevo';};
    mr.start();rec.textContent='Grabando…';setTimeout(()=>mr.state!=='inactive'&&mr.stop(),3000);}catch(e){rec.textContent='Error: '+errMsg(e);}};
  const v=await ui.verdict();
  return R(vs(v),'',{nivelPicoDb:db(peak),sonidoDetectado:hits>=6,dispositivo:st.getAudioTracks()[0].label||'(sin etiqueta)'});
}
const openCam=f=>navigator.mediaDevices.getUserMedia({video:{facingMode:{ideal:f},width:{ideal:1920},height:{ideal:1080}},audio:false});
function camInfo(st){
  const t=st.getVideoTracks()[0],s=t.getSettings();let c={};try{c=t.getCapabilities?t.getCapabilities():{};}catch{}
  return{etiqueta:t.label||'(sin etiqueta)',facingModeReportado:s.facingMode||'(n/d)',resolucionPista:s.width+'×'+s.height,fps:s.frameRate,estado:t.readyState,
    resolucionMaxima:c.width&&c.height?c.width.max+'×'+c.height.max:'(n/d)',linterna:!!c.torch,zoom:c.zoom?c.zoom.min+'–'+c.zoom.max:'no',enfoque:c.focusMode?c.focusMode.join(', '):'(n/d)'};
}
async function waitVideo(v,st){v.muted=true;v.playsInline=true;v.srcObject=st;await withTimeout(v.play(),4000,'La cámara no arrancó');
  for(let i=0;i<40&&!v.videoWidth;i++)await sleep(100);if(!v.videoWidth)throw new Error('La cámara no entregó imagen');}
const camErr=(e,f)=>e&&(e.name==='NotFoundError'||e.name==='OverconstrainedError')?'No se encontró cámara '+(f==='environment'?'trasera':'frontal'):gumErr(e);
const camMismatch=(i,f)=>i.facingModeReportado!=='(n/d)'&&i.facingModeReportado!==f?'Se pidió cámara '+(f==='environment'?'trasera':'frontal')+' pero se abrió "'+i.facingModeReportado+'" (probablemente no existe o no está disponible)':'';
function analyzeFrame(v){
  const w=320,h=Math.round(w*v.videoHeight/v.videoWidth)||240,c=document.createElement('canvas');c.width=w;c.height=h;
  const x=c.getContext('2d',{willReadFrequently:true});x.drawImage(v,0,0,w,h);
  const d=x.getImageData(0,0,w,h).data,g=new Float32Array(w*h);let sum=0,dark=0,burn=0;
  for(let i=0,j=0;i<d.length;i+=4,j++){const l=.2126*d[i]+.7152*d[i+1]+.0722*d[i+2];g[j]=l;sum+=l;if(l<10)dark++;if(l>245)burn++;}
  const mean=sum/g.length;let vr=0;for(const l of g)vr+=(l-mean)**2;
  const L=[];for(let y=1;y<h-1;y++)for(let xx=1;xx<w-1;xx++){const i=y*w+xx;L.push(4*g[i]-g[i-1]-g[i+1]-g[i-w]-g[i+w]);}
  const lm=L.reduce((a,b)=>a+b,0)/L.length;let lv=0;for(const l of L)lv+=(l-lm)**2;lv/=L.length;
  return{luminanciaMedia0a255:Math.round(mean),contraste:Math.round(Math.sqrt(vr/g.length)),nitidezLaplaciano:Math.round(lv),
    nitidezValoracion:lv>100?'nítida':lv>30?'media':'baja (borrosa, lente sucia o escena sin detalle)',pixelesMuyOscurosPct:fmt(dark/g.length*100,1),pixelesQuemadosPct:fmt(burn/g.length*100,1)};
}
const measureFps=v=>new Promise(res=>{if(!v.requestVideoFrameCallback)return res(null);let n=0,t0=null;const cb=(now)=>{if(t0==null)t0=now;else n++;if(now-t0<1000)v.requestVideoFrameCallback(cb);else res(fmt(n*1000/(now-t0),1));};v.requestVideoFrameCallback(cb);setTimeout(()=>res(null),2500);});
async function fullPhoto(st){
  try{if(!window.ImageCapture)return{error:'ImageCapture no disponible en este navegador'};
    const ic=new ImageCapture(st.getVideoTracks()[0]);let pc={};try{pc=await ic.getPhotoCapabilities();}catch{}
    const blob=await withTimeout(ic.takePhoto(),6000,'takePhoto sin respuesta'),bm=await createImageBitmap(blob);
    const o={ancho:bm.width,alto:bm.height,mp:fmt(bm.width*bm.height/1e6,1),kb:Math.round(blob.size/1024),
      maxFoto:pc.imageWidth&&pc.imageHeight?pc.imageWidth.max+'×'+pc.imageHeight.max+' ('+fmt(pc.imageWidth.max*pc.imageHeight.max/1e6,1)+' MP)':'(n/d)',flash:pc.fillLightMode?pc.fillLightMode.join(', '):'(n/d)',blob};
    if(bm.close)bm.close();return o;}catch(e){return{error:errMsg(e)};}
}
const photoTxt=p=>p?(p.error?'no disponible: '+p.error:p.ancho+'×'+p.alto+' ('+p.mp+' MP, '+p.kb+' KB) · máx. sensor '+p.maxFoto+' · flash '+p.flash):'no';
async function camAuto(f){
  if(!hasGUM())return R('unsupported','getUserMedia no disponible (¿falta HTTPS?)');
  let st;try{st=await openCam(f);}catch(e){return R('fail',camErr(e,f));}
  const v=document.createElement('video');
  try{await waitVideo(v,st);await sleep(500);
    const i=camInfo(st);i.resolucionVideo=v.videoWidth+'×'+v.videoHeight;
    const mm=camMismatch(i,f);if(mm)return R('fail',mm,i);
    Object.assign(i,analyzeFrame(v));i.fpsMedidos=(await measureFps(v))||'(n/d)';
    i.fotoCompleta=photoTxt(await fullPhoto(st));
    return R('ok',i.luminanciaMedia0a255<4?'Imagen casi negra: lente tapada o poca luz.':'Nitidez/contraste dependen de la escena: usa el test guiado apuntando a un texto.',i);
  }catch(e){return R('fail',errMsg(e));}finally{stopStream(st);v.srcObject=null;}
}
async function camGuided(ui,f){
  if(!hasGUM())return R('unsupported','getUserMedia no disponible (¿falta HTTPS?)');
  let st;try{st=await openCam(f);}catch(e){return R('fail',camErr(e,f));}
  ui.onCleanup(()=>stopStream(st));
  ui.body.innerHTML='<video id="cv" autoplay playsinline muted></video><p class="muted" id="cInfo">Abriendo…</p><p class="muted">Apunta a un texto o página con detalle y a una distancia de ~20 cm para medir la nitidez.</p><div class="grid2"><button class="btn" id="shot">📸 Foto a máxima resolución</button><button class="btn" id="torch" hidden>🔦 Linterna</button></div><div id="shotOut"></div>';
  const v=$('#cv');let info={},photo=null,torchOn=false,torchTried=false,q=null;
  try{await waitVideo(v,st);info=camInfo(st);info.resolucionVideo=v.videoWidth+'×'+v.videoHeight;info.fpsMedidos=(await measureFps(v))||'(n/d)';
    $('#cInfo').textContent=info.resolucionVideo+' · '+info.fpsMedidos+' fps · máx. '+info.resolucionMaxima+' · '+info.etiqueta;}
  catch(e){return R('fail',errMsg(e));}
  const mm=camMismatch(info,f);if(mm)$('#cInfo').textContent='⚠ '+mm;
  if(info.linterna)$('#torch').hidden=false;
  $('#torch').onclick=async()=>{torchTried=true;try{torchOn=!torchOn;await st.getVideoTracks()[0].applyConstraints({advanced:[{torch:torchOn}]});}catch(e){$('#cInfo').textContent='Linterna: '+errMsg(e);}};
  $('#shot').onclick=async()=>{$('#shot').textContent='Capturando…';q=analyzeFrame(v);photo=await fullPhoto(st);$('#shot').textContent='📸 Repetir foto';
    let url,extra='';
    if(photo&&photo.blob)url=URL.createObjectURL(photo.blob);
    else{const c=document.createElement('canvas');c.width=v.videoWidth;c.height=v.videoHeight;c.getContext('2d').drawImage(v,0,0);url=c.toDataURL('image/jpeg',.92);extra=' (captura de vídeo; takePhoto no disponible)';}
    $('#shotOut').innerHTML='<div class="card"><b>Foto:</b> '+esc(photoTxt(photo))+esc(extra)+'<pre>nitidez '+q.nitidezLaplaciano+' ('+esc(q.nitidezValoracion)+')\nluminancia '+q.luminanciaMedia0a255+'/255 · contraste '+q.contraste+'\noscuros '+q.pixelesMuyOscurosPct+'% · quemados '+q.pixelesQuemadosPct+'%</pre></div><img src="'+url+'" style="width:100%;border-radius:12px">';ui.suggest(true);};
  const r=await ui.verdict();
  if(torchOn)try{await st.getVideoTracks()[0].applyConstraints({advanced:[{torch:false}]});}catch{}
  if(q)Object.assign(info,q);info.fotoCompleta=photoTxt(photo);if(info.linterna)info.linternaProbada=torchTried?'sí':'no';
  return R(vs(r),r==='ok'&&mm?mm:'',info);
}
async function vibeAuto(){
  if(!navigator.vibrate)return R('unsupported','Vibration API no disponible (iOS/Safari y Firefox móvil no la soportan)');
  return navigator.vibrate(250)?R('manual','vibrate() aceptado; confirma que lo sentiste en el test guiado.',{vibrateDevuelve:true}):R('fail','vibrate() devolvió false (bloqueado: sin interacción previa, modo ahorro/silencio o sin motor)',{vibrateDevuelve:false});
}
async function vibeGuided(ui){
  if(!navigator.vibrate)return R('unsupported','Vibration API no disponible');
  const P={c:['Corta 200 ms',200],m:['Media 500 ms',500],p:['Patrón',[100,50,100,50,300]],l:['Larga 1 s',1000],r:['Repetida ~3 s',[400,150,400,150,400,150,400,150,400]]};
  ui.body.innerHTML='<p>Sujeta el teléfono con la pantalla encendida y pulsa cada patrón. Debajo verás lo que responde el navegador.</p><div class="grid2">'+Object.entries(P).map(([k,[n]])=>'<button class="btn" data-p="'+k+'">'+n+'</button>').join('')+'</div><pre id="vLog">(sin pulsaciones)</pre><div class="card"><b>Si el navegador dice «true» pero no vibra:</b><pre>• Ajustes › Sonido y vibración: activa la vibración y sube su intensidad (en algunos móviles hay un control aparte para «multimedia/notificaciones»).\n• Quita modo silencio, No molestar y ahorro de batería.\n• Prueba en Chrome (no en navegadores integrados de apps).\n• Si vibra al teclear pero aquí no, es una limitación del fabricante/Chrome: márcalo como Fallo.</pre></div>';
  const tried=[],log=[];let blocked=0;ui.onCleanup(()=>navigator.vibrate(0));
  ui.body.addEventListener('click',e=>{const b=e.target.closest('[data-p]');if(!b)return;const p=P[b.dataset.p];tried.push(p[0]);
    let ok;try{ok=navigator.vibrate(p[1]);}catch(er){ok='error '+errMsg(er);}if(ok!==true)blocked++;
    log.push(new Date().toLocaleTimeString()+'  '+p[0]+' → vibrate() devolvió '+ok);$('#vLog').textContent=log.slice(-6).join('\n');});
  const v=await ui.verdict();
  return R(vs(v),blocked?'vibrate() devolvió false/error '+blocked+' vez/veces (el navegador bloqueó la orden)':(v==='fail'&&tried.length?'El navegador aceptó la orden pero el usuario no sintió vibración (ajustes del sistema o limitación del fabricante)':(v==='ok'&&!tried.length?'Marcado OK sin probar ningún patrón':'')),{patronesProbados:tried.join(', ')||'ninguno',ordenesAceptadas:tried.length-blocked,ordenesBloqueadas:blocked});
}
async function batteryGuided(ui){
  const b=navigator.getBattery?await navigator.getBattery().catch(()=>null):null;
  ui.body.innerHTML='<div class="card"><b>Lo que ve el navegador</b><pre id="bLive">'+(b?'':'API de batería no disponible')+'</pre></div><div class="card"><b>Salud y ciclos de carga</b><p class="muted">Ningún navegador puede leer la salud ni los ciclos de la batería: Android no los expone a las páginas web. Mira el dato en el propio móvil y escríbelo aquí para que quede en el informe:</p><pre>• Pixel (Android 14+): Ajustes › Batería › Estado de la batería.\n• Samsung: app Samsung Members › Diagnóstico › Batería, o marca *#0228# y mira «LEVEL/Capacity».\n• Otras marcas: marcador *#*#4636#*#* › Información de la batería, o una app como AccuBattery.</pre><label class="chk">Salud (%) <input id="bH" type="number" inputmode="numeric" min="0" max="100" style="width:90px;min-height:44px;font-size:16px"></label><label class="chk">Ciclos <input id="bC" type="number" inputmode="numeric" min="0" style="width:90px;min-height:44px;font-size:16px"></label></div>';
  if(b){const up=()=>{$('#bLive')&&($('#bLive').textContent='Nivel '+Math.round(b.level*100)+'% · '+(b.charging?'cargando':'descargando')+'\nHasta carga: '+(b.chargingTime===Infinity?'∞':b.chargingTime+' s')+'\nHasta descarga: '+(b.dischargingTime===Infinity?'∞':b.dischargingTime+' s'));};
    up();['levelchange','chargingchange','chargingtimechange','dischargingtimechange'].forEach(e=>b.addEventListener(e,up));ui.onCleanup(()=>['levelchange','chargingchange','chargingtimechange','dischargingtimechange'].forEach(e=>b.removeEventListener(e,up)));}
  const v=await ui.verdict();
  const h=$('#bH').value,c=$('#bC').value,d={};
  if(b){d.nivel=Math.round(b.level*100)+'%';d.cargando=b.charging;}
  d.saludBateriaPct=h!==''?h+' (introducido a mano)':'no indicada';d.ciclosCarga=c!==''?c+' (introducido a mano)':'no indicados';
  let note='';if(h!==''&&+h<80)note='Salud baja (<80%): la batería está degradada.';
  return R(vs(v),note,d);
}

/* ---------- Pantalla y táctil (guiadas) ---------- */
const FILLS=[['Rojo','#f00'],['Verde','#0f0'],['Azul','#00f'],['Blanco','#fff'],['Negro','#000'],['Gris 50%','#808080'],['Degradado gris','linear-gradient(90deg,#000,#fff)'],
  ['Degradado RGB','linear-gradient(90deg,#f00,#ff0,#0f0,#0ff,#00f,#f0f,#f00)'],
  ['Bandas de gris (16)','linear-gradient(90deg,'+Array.from({length:16},(_,i)=>{const g=Math.round(i*255/15);return'rgb('+g+','+g+','+g+') '+i*6.25+'% '+(i+1)*6.25+'%';}).join(',')+')']];
function runColors(){return new Promise(res=>{
  const fs=$('#fs'),lb=$('#fsLbl');let i=0;
  const close=()=>{fs.hidden=true;fs.onclick=null;if(document.fullscreenElement)document.exitFullscreen().catch(()=>{});res();};
  const show=()=>{if(i>=FILLS.length)return close();fs.style.background=FILLS[i][1];lb.textContent=FILLS[i][0]+' · '+(i+1)+'/'+FILLS.length+' · toca para avanzar';lb.style.animation='none';void lb.offsetWidth;lb.style.animation='';};
  fs.hidden=false;try{fs.requestFullscreen&&fs.requestFullscreen({navigationUI:'hide'}).catch(()=>{});}catch{}
  fs.onclick=()=>{i++;show();};show();});}
async function displayGuided(ui){
  ui.body.innerHTML='<p>Se mostrarán colores y degradados a pantalla completa. <b>Toca para avanzar.</b> Busca píxeles muertos o atascados, manchas, quemaduras, líneas, bandas o zonas con otro tono. Sube el brillo.</p><button class="btn primary" id="dStart" style="width:100%">▶ Iniciar prueba de pantalla</button><p class="muted" id="dInfo"></p>';
  let done=false;
  ui.onCleanup(()=>{const fs=$('#fs');fs.hidden=true;fs.onclick=null;if(document.fullscreenElement)document.exitFullscreen().catch(()=>{});});
  $('#dStart').onclick=async()=>{await runColors();done=true;$('#dInfo').textContent='Prueba completada. ¿Viste algún defecto? Si no → OK.';ui.suggest(true);};
  const v=await ui.verdict();
  return R(vs(v),v==='ok'&&!done?'Marcado OK sin completar la secuencia de colores':'',{coloresMostrados:done?FILLS.map(f=>f[0]).join(', '):'secuencia incompleta',resolucion:screen.width+'×'+screen.height+' @'+fmt(devicePixelRatio,2)+'x'});
}
async function touchGuided(ui){
  ui.body.innerHTML='<div class="big-n"><b id="tNow">0</b> ahora · <b id="tMax">0</b> máx. simultáneos · <b id="tTot">0</b> toques</div><canvas id="tc"></canvas><pre id="tList"></pre><p class="muted">Apoya 2, 3, 4, 5… dedos a la vez y arrastra por toda la superficie, esquinas incluidas. Si alguna zona no dibuja → Fallo.</p>';
  const cv=$('#tc'),dpr=devicePixelRatio||1,W=Math.max(200,ui.body.clientWidth-28),H=Math.max(240,Math.round(innerHeight*.4));
  cv.style.height=H+'px';cv.width=Math.round(W*dpr);cv.height=Math.round(H*dpr);
  const x=cv.getContext('2d');x.scale(dpr,dpr);
  const COL=['#ef4444','#22c55e','#3b82f6','#f59e0b','#a855f7','#06b6d4','#ec4899','#84cc16','#f97316','#14b8a6'];
  const pts=new Map(),segs=[];let max=0,total=0,ptype='?';
  const draw=()=>{x.clearRect(0,0,W,H);x.lineWidth=4;x.lineCap='round';
    for(const s of segs){x.strokeStyle=s.c;x.beginPath();x.moveTo(s.a,s.b);x.lineTo(s.x,s.y);x.stroke();}
    let n=0;for(const[,p]of pts){n++;x.fillStyle=p.c;x.globalAlpha=.55;x.beginPath();x.arc(p.x,p.y,30,0,7);x.fill();x.globalAlpha=1;x.fillStyle='#fff';x.font='bold 16px sans-serif';x.textAlign='center';x.fillText(n,p.x,p.y+6);}
    $('#tNow').textContent=pts.size;$('#tMax').textContent=max;$('#tTot').textContent=total;
    $('#tList').textContent=[...pts.values()].map((p,i)=>'#'+(i+1)+'  x '+Math.round(p.x)+'  y '+Math.round(p.y)).join('\n');};
  const pos=e=>{const r=cv.getBoundingClientRect();return[(e.clientX-r.left)*W/r.width,(e.clientY-r.top)*H/r.height];};
  cv.addEventListener('pointerdown',e=>{e.preventDefault();ptype=e.pointerType;try{cv.setPointerCapture(e.pointerId);}catch{}const[a,b]=pos(e);pts.set(e.pointerId,{x:a,y:b,c:COL[total%COL.length]});total++;max=Math.max(max,pts.size);if(max>=2)ui.suggest(true);draw();});
  cv.addEventListener('pointermove',e=>{const p=pts.get(e.pointerId);if(!p)return;const[a,b]=pos(e);segs.push({a:p.x,b:p.y,x:a,y:b,c:p.c});if(segs.length>3000)segs.shift();p.x=a;p.y=b;draw();});
  const up=e=>{pts.delete(e.pointerId);draw();};cv.addEventListener('pointerup',up);cv.addEventListener('pointercancel',up);
  draw();
  const v=await ui.verdict();
  return R(vs(v),v==='ok'&&max<2?'Marcado OK pero solo se registró 1 toque simultáneo (multitouch no verificado)':'',{maxToquesSimultaneos:max,toquesTotales:total,maxTouchPointsDeclarado:navigator.maxTouchPoints||0,tipoPuntero:ptype});
}
async function sensorsGuided(ui){
  if(!('DeviceMotionEvent' in window)&&!('DeviceOrientationEvent' in window))return R('unsupported','API DeviceMotion/Orientation no disponible');
  ui.body.innerHTML='<p>Mueve, inclina y gira el teléfono. Cada sensor se marcará al detectar cambios.</p><div id="sPerm"></div>'+['A|Acelerómetro','G|Giroscopio','O|Orientación y brújula'].map(s=>{const[k,n]=s.split('|');return'<div class="card"><b>'+n+'</b><span class="tick" id="t'+k+'">…</span><pre id="v'+k+'"></pre></div>';}).join('');
  const m=new SensorMonitor();
  if(typeof DeviceMotionEvent.requestPermission==='function'){
    $('#sPerm').innerHTML='<button class="btn primary" id="sp" style="width:100%">Conceder permiso de sensores</button>';
    $('#sp').onclick=async()=>{try{await DeviceMotionEvent.requestPermission();await DeviceOrientationEvent.requestPermission();}catch{}};}
  m.start();ui.onCleanup(()=>m.stop());
  const render=()=>{const l=m.last,ch=m.changed(TH_GUIDED),set=(k,c,t)=>{$('#t'+k).textContent=c?'✓ cambió':(t?'… mueve':'sin datos');$('#t'+k).style.color=c?'var(--ok)':'var(--mut)';};
    $('#vA').textContent=m.n.accel?'x/y/z: '+xyz(l.accel)+' m/s²':'sin datos';$('#vG').textContent=m.n.gyro?'α/β/γ: '+xyz(l.gyro,['alpha','beta','gamma'])+' °/s':'sin datos';
    $('#vO').textContent=m.n.orient?'α '+fmt(l.orient.alpha,0)+' β '+fmt(l.orient.beta,0)+' γ '+fmt(l.orient.gamma,0)+' · rumbo '+(l.heading!=null?Math.round(l.heading)+'°':'—')+(m.hasAbs?' (magnético)':' (relativo)'):'sin datos';
    set('A',ch.accel,m.n.accel);set('G',ch.gyro,m.n.gyro);set('O',ch.orient,m.n.orient);if(ch.accel&&ch.gyro&&ch.orient)ui.suggest(true);};
  const iv=setInterval(render,200);ui.onCleanup(()=>clearInterval(iv));
  const v=await ui.verdict();m.stop();const ev=evalSensors(m,TH_GUIDED);
  if(v==='ok')return R('ok',ev.status==='ok'?'':'Marcado OK por el usuario. '+ev.note,ev.data);
  if(v==='fail')return R('fail',ev.note||'Marcado como Fallo por el usuario',ev.data);
  return R(null);
}

/* ---------- Catálogo de pruebas ---------- */
const cam=(f,n)=>({id:f==='environment'?'cam_rear':'cam_front',group:'Cámara',name:n,desc:'Resolución, nitidez, fps y foto máx.',est:f==='environment'?10:10,eA:4,timeout:30000,auto:()=>camAuto(f),guided:ui=>camGuided(ui,f)});
const TESTS=[
 {id:'env',group:'Entorno',name:'Dispositivo y navegador',desc:'Modelo, CPU, memoria, user-agent',est:1,eA:1,auto:envAuto},
 {id:'caps',group:'Entorno',name:'Capacidades del navegador',desc:'WebGL, WebRTC, Wake Lock, portapapeles',est:2,eA:2,auto:capsAuto},
 {id:'screen',group:'Pantalla y táctil',name:'Resolución y orientación',desc:'Resolución, DPR, orientación, refresco',est:1,eA:1,auto:screenAuto},
 {id:'display',group:'Pantalla y táctil',name:'Color y píxeles muertos',desc:'Rojo, verde, azul, blanco, negro, degradados',est:15,guided:displayGuided},
 {id:'touch',group:'Pantalla y táctil',name:'Multitouch',desc:'Toques simultáneos y coordenadas',est:12,eA:.5,auto:touchAuto,guided:touchGuided},
 {id:'sensors',group:'Sensores',name:'Acelerómetro, giroscopio y brújula',desc:'Lecturas en vivo y cambios al mover',est:15,eA:2.5,auto:sensorsAuto,guided:sensorsGuided},
 {id:'audio',group:'Audio',name:'Altavoz (canales L/R)',desc:'Tonos izquierdo, derecho y barrido',est:15,eA:1,auto:audioAuto,guided:audioGuided},
 {id:'mic',group:'Audio',name:'Micrófono',desc:'Medidor de nivel y grabación',est:12,eA:3,timeout:30000,auto:micAuto,guided:micGuided},
 cam('environment','Cámara trasera'),cam('user','Cámara frontal'),
 {id:'vibe',group:'Vibración',name:'Motor de vibración',desc:'Patrones corto, medio y largo',est:8,eA:1,auto:vibeAuto,guided:vibeGuided},
 {id:'net',group:'Conectividad',name:'Red y latencia',desc:'Estado, tipo de conexión, latencia, descarga',est:5,eA:5,timeout:40000,auto:netAuto},
 {id:'geo',group:'Ubicación',name:'GPS / geolocalización',desc:'Latitud, longitud, precisión, tiempo',est:6,eA:6,timeout:40000,auto:geoAuto},
 {id:'battery',group:'Batería',name:'Batería',desc:'Nivel, carga, salud y ciclos (manual)',est:12,eA:1,auto:batteryAuto,guided:batteryGuided}
];
const byId=id=>TESTS.find(t=>t.id===id);
const cost=(t,m)=>m==='guided'?t.est:(t.eA||t.est);
const quickItems=()=>TESTS.filter(t=>t.auto).map(t=>({test:t,mode:'auto'}));
const guidedItems=()=>TESTS.filter(t=>t.guided).map(t=>({test:t,mode:'guided'}));
const allItems=()=>[...TESTS.filter(t=>!t.guided).map(t=>({test:t,mode:'auto'})),...guidedItems()];

/* ---------- Ejecución ---------- */
let running=false,runningId=null,current=null,wl=null;
const toast=m=>{const t=$('#toast');t.textContent=m;t.classList.add('on');clearTimeout(toast.t);toast.t=setTimeout(()=>t.classList.remove('on'),2200);};
async function keepAwake(on){try{if(on&&navigator.wakeLock)wl=await navigator.wakeLock.request('screen');else if(wl){await wl.release();wl=null;}}catch{}}
function setProgress(done,total,label){
  const pct=total?Math.round(done/total*100):0,rem=Math.max(0,Math.round(total-done));
  ['#bar','#sBar'].forEach(s=>$(s).style.width=pct+'%');
  const t=(label?label+' · ':'')+pct+'% · ≈ '+(rem<60?rem+' s':Math.ceil(rem/60)+' min')+' restantes';
  $('#progTxt').textContent=t;$('#sEta').textContent=t;
}
function makeUI(test,idx,total){
  $('#sTitle').textContent=test.name;$('#sStep').textContent='Paso '+(idx+1)+' de '+total;$('#sBody').innerHTML='';$('#vOk').classList.remove('suggest');
  let resolve;const p=new Promise(r=>resolve=r),cl=[];
  const ui={body:$('#sBody'),aborted:false,verdict:()=>p,resolve:v=>resolve(v),suggest:(on=true)=>$('#vOk').classList.toggle('suggest',on),onCleanup:f=>cl.push(f),
    cleanup(){cl.splice(0).reverse().forEach(f=>{try{f()}catch{}});$('#sBody').innerHTML='';$('#vOk').classList.remove('suggest');}};
  current=ui;return ui;
}
$('#vOk').onclick=()=>current&&current.resolve('ok');
$('#vFail').onclick=()=>current&&current.resolve('fail');
$('#vSkip').onclick=()=>current&&current.resolve('skip');
$('#sAbort').onclick=()=>{if(current){current.aborted=true;current.resolve('skip');}};
async function runQueue(items){
  if(running||!items.length)return;running=true;runningId=null;document.body.classList.add('busy');$('#prog').hidden=false;await keepAwake(true);
  const total=items.reduce((s,i)=>s+cost(i.test,i.mode),0),nG=items.filter(i=>i.mode==='guided').length;let done=0,gi=0,aborted=false;
  try{for(const{test,mode}of items){
    setProgress(done,total,test.name);const t0=performance.now();let r;
    if(mode==='guided'){
      $('#stage').hidden=false;document.body.classList.add('noscroll');
      const ui=makeUI(test,gi++,nG);
      try{r=await test.guided(ui);}catch(e){r=R('fail',errMsg(e));}finally{ui.cleanup();}
      if(ui.aborted){aborted=true;break;}
    }else{
      $('#stage').hidden=true;document.body.classList.remove('noscroll');runningId=test.id;renderList();
      try{r=await withTimeout(test.auto(),test.timeout||25000);}catch(e){r=R('fail',errMsg(e));}
      runningId=null;
    }
    if(r.status==null){if(!results[test.id])results[test.id]={status:'manual',note:'Omitida (sin verificar)',data:{},ms:0,mode};}
    else results[test.id]={status:r.status,note:r.note||'',data:r.data||{},ms:Math.round(performance.now()-t0),mode};
    done+=cost(test,mode);renderList();
  }}finally{
    $('#stage').hidden=true;document.body.classList.remove('noscroll');document.body.classList.remove('busy');
    running=false;runningId=null;await keepAwake(false);setProgress(total,total,'Terminado');setTimeout(()=>{if(!running)$('#prog').hidden=true;},2500);renderList();
  }
  toast(aborted?'Flujo cancelado':'Pruebas terminadas');
  if(items.length>1)switchTab('report');
}

/* ---------- Informe ---------- */
const hum=k=>k.replace(/_/g,' ').replace(/([a-z0-9])([A-Z])/g,'$1 $2');
function flatten(o,pre='',d=0){const out=[];if(o==null)return out;
  for(const[k,v]of Object.entries(o)){const key=pre+hum(k);
    if(v&&typeof v==='object'&&!Array.isArray(v)&&d<2)out.push(...flatten(v,key+' › ',d+1));
    else out.push([key,Array.isArray(v)?v.join(', '):v===true?'sí':v===false?'no':v==null?'—':String(v)]);}
  return out;}
const showCoords=()=>$('#chkCoords').checked;
function dataFor(t){const r=results[t.id];if(!r)return{};const d=JSON.parse(JSON.stringify(r.data||{}));
  if(t.id==='geo'&&!showCoords()){['latitud','longitud','altitudM'].forEach(k=>{if(k in d)d[k]='(oculto)';});}return d;}
function counts(){const c={ok:0,fail:0,unsupported:0,manual:0,pending:0};TESTS.forEach(t=>c[(results[t.id]||{status:'pending'}).status]++);return c;}
function buildReport(){
  const c=counts(),e=results.env?results.env.data:{};
  return{app:'Diagnóstico Android',version:VERSION,fecha:new Date().toISOString(),
    dispositivo:{userAgent:navigator.userAgent,modelo:e.modelo||null,pantalla:screen.width+'×'+screen.height+' @'+fmt(devicePixelRatio,2)+'x',url:location.origin},
    resumen:{...c,total:TESTS.length},
    pruebas:TESTS.map(t=>{const r=results[t.id];const s=r?r.status:'pending';return{id:t.id,grupo:t.group,nombre:t.name,estado:s,estadoEtiqueta:ST[s].label,nota:r?r.note:'',modo:r?r.mode:null,duracionMs:r?r.ms:null,datos:dataFor(t)};})};
}
function textReport(){
  const rp=buildReport(),c=rp.resumen,L=['📱 DIAGNÓSTICO DE TELÉFONO','Fecha: '+new Date().toLocaleString(),
    'Dispositivo: '+(rp.dispositivo.modelo&&rp.dispositivo.modelo!=='(no expuesto)'?rp.dispositivo.modelo+' · ':'')+rp.dispositivo.pantalla,'UA: '+rp.dispositivo.userAgent,'',
    '✅ '+c.ok+' OK · ❌ '+c.fail+' Fallo · 🚫 '+c.unsupported+' No soportado · ✋ '+c.manual+' Manual · ⏳ '+c.pending+' Pendiente',''];
  rp.pruebas.forEach(p=>{L.push(ST[p.estado].icon+' '+p.nombre+': '+p.estadoEtiqueta);if(p.nota)L.push('   ⚠ '+p.nota);flatten(p.datos).forEach(([k,v])=>L.push('   • '+k+': '+v));L.push('');});
  return L.join('\n').trim();
}
function renderReport(){
  const c=counts(),n=TESTS.length,col={ok:'var(--ok)',fail:'var(--fail)',unsupported:'var(--uns)',manual:'var(--man)',pending:'var(--pen)'};
  $('#repSummary').innerHTML='<b>'+c.ok+' de '+n+' pruebas OK</b><div class="stack">'+Object.keys(col).map(k=>'<i style="width:'+c[k]/n*100+'%;background:'+col[k]+'"></i>').join('')+'</div><div class="chips">'+Object.keys(col).map(k=>'<span class="chip '+k+'">'+ST[k].label+' '+c[k]+'</span>').join('')+'</div>';
  $('#repList').innerHTML=TESTS.map(t=>{const r=results[t.id],s=r?r.status:'pending',ln=flatten(dataFor(t));
    return'<details class="card"'+(s==='fail'?' open':'')+'><summary><span class="chip '+s+'">'+ST[s].label+'</span><b>'+esc(t.name)+'</b></summary>'+(r&&r.note?'<p class="note">'+esc(r.note)+'</p>':'')+
      (ln.length?'<dl>'+ln.map(([k,v])=>'<dt>'+esc(k)+'</dt><dd>'+esc(v)+'</dd>').join('')+'</dl>':'<p class="muted">Sin datos todavía.</p>')+
      '<button class="mini" data-run="'+t.id+'" data-mode="'+(t.guided?'guided':'auto')+'">↻ Repetir</button></details>';}).join('');
}
function renderList(){
  const groups=[...new Set(TESTS.map(t=>t.group))];
  $('#list').innerHTML=groups.map(g=>'<h2>'+g+'</h2>'+TESTS.filter(t=>t.group===g).map(t=>{const r=results[t.id],s=r?r.status:'pending';
    return'<div class="row"><div class="rmain"><div class="rname">'+ST[s].icon+' '+esc(t.name)+'</div><div class="rnote">'+esc(r&&r.note?r.note:t.desc)+'</div></div><span class="chip '+s+'">'+(runningId===t.id?'Probando…':ST[s].label)+'</span><div class="rbtns">'+
      (t.auto?'<button class="mini" data-run="'+t.id+'" data-mode="auto">Auto</button>':'')+(t.guided?'<button class="mini" data-run="'+t.id+'" data-mode="guided">Guiado</button>':'')+'</div></div>';}).join('')).join('');
  const c=counts();$('#tabBadge').textContent=c.fail?'❌'+c.fail:'';
  if(!$('#report').hidden)renderReport();
}
function switchTab(t){document.querySelectorAll('.tabs button').forEach(b=>b.classList.toggle('on',b.dataset.tab===t));$('#home').hidden=t!=='home';$('#report').hidden=t!=='report';if(t==='report')renderReport();window.scrollTo(0,0);}
async function copyText(txt){try{await navigator.clipboard.writeText(txt);return true;}catch{try{const a=document.createElement('textarea');a.value=txt;a.style.cssText='position:fixed;opacity:0';document.body.appendChild(a);a.select();const ok=document.execCommand('copy');a.remove();return ok;}catch{return false;}}}
function download(name,mime,txt){const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([txt],{type:mime}));a.download=name;document.body.appendChild(a);a.click();setTimeout(()=>{URL.revokeObjectURL(a.href);a.remove();},1000);}
const stamp=()=>new Date().toISOString().slice(0,16).replace(/[-:T]/g,'');
const estTxt=s=>'≈ '+(s<90?Math.max(5,Math.round(s/5)*5)+' s':fmt(s/60,1).toString().replace('.',',')+' min');

/* ---------- Init ---------- */
document.addEventListener('click',e=>{const b=e.target.closest('[data-run]');if(b)runQueue([{test:byId(b.dataset.run),mode:b.dataset.mode}]);});
document.querySelectorAll('.tabs button').forEach(b=>b.onclick=()=>switchTab(b.dataset.tab));
$('#btnQuick').onclick=()=>runQueue(quickItems());
$('#btnGuided').onclick=()=>runQueue(guidedItems());
$('#btnAll').onclick=()=>runQueue(allItems());
$('#btnRetry').onclick=()=>{const it=TESTS.filter(t=>{const s=(results[t.id]||{status:'pending'}).status;return s==='fail'||s==='pending';}).map(t=>({test:t,mode:t.guided?'guided':'auto'}));it.length?runQueue(it):toast('No hay pruebas fallidas ni pendientes');};
$('#btnCopy').onclick=async()=>toast(await copyText(textReport())?'Informe copiado ✓':'No se pudo copiar');
$('#btnJson').onclick=()=>download('diagnostico-android-'+stamp()+'.json','application/json',JSON.stringify(buildReport(),null,2));
$('#btnTxt').onclick=()=>download('diagnostico-android-'+stamp()+'.txt','text/plain',textReport());
if(navigator.share){$('#btnShare').hidden=false;$('#btnShare').onclick=()=>navigator.share({title:'Diagnóstico de teléfono',text:textReport()}).catch(()=>{});}
$('#btnReset').onclick=()=>{if(confirm('¿Borrar todos los resultados?')){Object.keys(results).forEach(k=>delete results[k]);renderList();renderReport();toast('Reiniciado');}};
$('#chkCoords').onchange=renderReport;
const THEMES=['dark','light','contrast'];
function setTheme(t){document.documentElement.dataset.theme=t;try{localStorage.setItem('diag-theme',t);}catch{}}
let th0=null;try{th0=localStorage.getItem('diag-theme');}catch{}
setTheme(th0||(matchMedia('(prefers-color-scheme: light)').matches?'light':'dark'));
$('#btnTheme').onclick=()=>{const t=THEMES[(THEMES.indexOf(document.documentElement.dataset.theme)+1)%3];setTheme(t);toast('Tema: '+({dark:'oscuro',light:'claro',contrast:'alto contraste'})[t]);};
$('#estQuick').textContent=estTxt(quickItems().reduce((s,i)=>s+cost(i.test,i.mode),0));
$('#estGuided').textContent=estTxt(guidedItems().reduce((s,i)=>s+cost(i.test,i.mode),0));
$('#estAll').textContent=estTxt(allItems().reduce((s,i)=>s+cost(i.test,i.mode),0));
renderList();
})();
