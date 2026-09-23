'use strict';
const COLS=10, ROWS=20, HID=2;
let CELL=30, BX=150, BY=30; // mutable: versus mode uses a smaller layout
const LOCK_DELAY=500, MAX_RESETS=15, QUIT_HOLD=900; // ms of held ESC to quit, tetr.io-style
let DAS=110, ARR=25, SOFT=100;
function lsGet(k,def){try{const v=JSON.parse(localStorage.getItem(k));return v??def}catch(e){}return def}
function lsSet(k,v){try{localStorage.setItem(k,JSON.stringify(v))}catch(e){}}
const h=lsGet('webtris_handling',{});if(h.das)DAS=h.das;if(h.arr)ARR=h.arr;if(h.soft!=null)SOFT=h.soft;
let VOL=lsGet('webtris_vol',80), MUTE=lsGet('webtris_mute',false);
const gp=lsGet('webtris_gameplay',{}); // ponytail: one key for all gameplay visuals
let GRIDV=gp.grid??10, BGV=gp.board??80, SHADV=gp.shadow??40, ACTTX=gp.act||'ALL';
let COLORGHOST=gp.colorGhost??false, GRAYHOLD=gp.grayHold??true;
function saveGp(){lsSet('webtris_gameplay',{grid:GRIDV,board:BGV,shadow:SHADV,act:ACTTX,colorGhost:COLORGHOST,grayHold:GRAYHOLD});}
let openSec=null; // settings accordion, one open at a time
const DEFAULT_KEYS={left:'ArrowLeft',right:'ArrowRight',softDrop:'ArrowDown',rotCCW:'KeyZ',rotCW:'KeyX',hardDrop:'Space',hold:'KeyC',retry:'KeyR',quit:'Escape'};
let keybinds={};
keybinds={...DEFAULT_KEYS,...lsGet('webtris_keys',{})};
delete keybinds.pause;if(keybinds.quit=='KeyQ')keybinds.quit='Escape'; // ponytail: migrate pre-removal defaults
// versus/blitz attack table (ponytail: standard modern versus, no all-spin/surge variants)
const ATK={n:[0,1,2,4],ts:[0,2,4,6]},CMB=[0,1,1,2,2,3,3,4];
const cvs=document.getElementById('c'), ctx=cvs.getContext('2d');
const quitEl=document.getElementById('quitbar'); // ponytail: full-width hold-to-quit bar, DOM so it spans the screen
// ponytail: menu fills the window so buttons reach the real screen edge; play stays 600x660 centered
function goMenu(){state='menu';cvs.width=innerWidth;cvs.height=innerHeight;}
function goPlay(){cvs.width=600;cvs.height=660;}

const SHAPES={
  I:{m:[[0,0,0,0],[1,1,1,1],[0,0,0,0],[0,0,0,0]],c:'#2fd4e8'},
  O:{m:[[1,1],[1,1]],c:'#f7d308'},
  T:{m:[[0,1,0],[1,1,1],[0,0,0]],c:'#b93fe0'},
  S:{m:[[0,1,1],[1,1,0],[0,0,0]],c:'#3ecf4a'},
  Z:{m:[[1,1,0],[0,1,1],[0,0,0]],c:'#ef4a4a'},
  J:{m:[[1,0,0],[1,1,1],[0,0,0]],c:'#4a68ef'},
  L:{m:[[0,0,1],[1,1,1],[0,0,0]],c:'#f7941e'},
  G:{m:[],c:'#5f6673'}, // garbage row filler (color only)
};
// SRS wall kicks, +y up (negate y when applying)
const KJ={
 '01':[[0,0],[-1,0],[-1,1],[0,-2],[-1,-2]],'10':[[0,0],[1,0],[1,-1],[0,2],[1,2]],
 '12':[[0,0],[1,0],[1,-1],[0,2],[1,2]],'21':[[0,0],[-1,0],[-1,1],[0,-2],[-1,-2]],
 '23':[[0,0],[1,0],[1,1],[0,-2],[1,-2]],'32':[[0,0],[-1,0],[-1,-1],[0,2],[-1,2]],
 '30':[[0,0],[-1,0],[-1,-1],[0,2],[-1,2]],'03':[[0,0],[1,0],[1,1],[0,-2],[1,-2]],
};
const KI={
 '01':[[0,0],[-2,0],[1,0],[-2,-1],[1,2]],'10':[[0,0],[2,0],[-1,0],[2,1],[-1,-2]],
 '12':[[0,0],[-1,0],[2,0],[-1,2],[2,-1]],'21':[[0,0],[1,0],[-2,0],[1,-2],[-2,1]],
 '23':[[0,0],[2,0],[-1,0],[2,1],[-1,-2]],'32':[[0,0],[-2,0],[1,0],[-2,-1],[1,2]],
 '30':[[0,0],[1,0],[-2,0],[1,-2],[-2,1]],'03':[[0,0],[-1,0],[2,0],[-1,2],[2,-1]],
};
const MODES={
  sprint:{label:'SPRINT 40L',sub:'clear 40 lines fast',goal:40,accent:'#2fd4e8',mino:'I'},
  ultra:{label:'BLITZ',sub:'two-minute rush',time:120000,accent:'#f7941e',mino:'L'},
  marathon:{label:'MARATHON',sub:'150 line run',goal:150,accent:'#b93fe0',mino:'T'},
  zen:{label:'ZEN',sub:'endless mode',accent:'#3ecf4a',mino:'S'},
  versus:{label:'VS AI',sub:'fight the cpu',accent:'#ef4a4a',mino:'Z'},
};
const KEY_ACTIONS=[
  {id:'left',label:'Move Left'},{id:'right',label:'Move Right'},{id:'softDrop',label:'Soft Drop'},
  {id:'rotCCW',label:'Rotate CCW'},{id:'rotCW',label:'Rotate CW'},{id:'hardDrop',label:'Hard Drop'},
  {id:'hold',label:'Hold'},{id:'retry',label:'Retry'},{id:'quit',label:'Quit'},
];

let board, bag, cur, hold, canHold, state='menu', mode=null;
let menuHover=[0,0,0,0,0,0]; // per-row glow fade (0→1)
let backHover=0; // settings BACK bar uses the same menu hover animation
let lines, score, level, combo, b2b, pieces, time, gravAcc, lockT, resets, tspinFlag;
let flashes=[], popups=[], lands=[], drops=[], shines=[], spawnT=0;
let moveDir=0, dasT=0, arrT=0, prevIv=0, quitHold=0;
let vs=null; // versus match state, set by startVs()
const keys={};
let rebindAction=null;
let clickZones=[];
let needsDraw=true,lastState=state;
const reducedMotionQuery=matchMedia('(prefers-reduced-motion: reduce)');
let reducedMotion=reducedMotionQuery.matches;
reducedMotionQuery.addEventListener('change',e=>{reducedMotion=e.matches;needsDraw=true;});
let best={};
let mouseX=-1,mouseY=-1; // ponytail: hover state via raw coords, no React state equivalent
best=lsGet('webtris_best',{});

// --- audio: tiny beeper, no assets ---
let AC;
function beep(f,d=0.06,type='square',v=0.04){
  try{
    if(MUTE||VOL<=0)return;
    AC=AC||new (window.AudioContext||window.webkitAudioContext)();
    const o=AC.createOscillator(),g=AC.createGain();
    o.type=type;o.frequency.value=f;g.gain.value=v*VOL/80;
    g.gain.exponentialRampToValueAtTime(0.001,AC.currentTime+d);
    o.connect(g);g.connect(AC.destination);o.start();o.stop(AC.currentTime+d);
  }catch(e){}
}

function rotateM(m,dir){
  const n=m.length,r=m.map(row=>row.slice());
  for(let y=0;y<n;y++)for(let x=0;x<n;x++){
    if(dir>0) r[x][n-1-y]=m[y][x]; else r[n-1-x][y]=m[y][x];
  }
  return r;
}
function refill(b){
  const a=['I','J','L','O','S','T','Z'];
  for(let i=6;i>0;i--){const j=Math.random()*(i+1)|0;[a[i],a[j]]=[a[j],a[i]];}
  b.push(...a);
}
function collide(bd,m,px,py){
  for(let y=0;y<m.length;y++)for(let x=0;x<m[y].length;x++){
    if(!m[y][x])continue;
    const bx=px+x,by=py+y;
    if(bx<0||bx>=COLS||by>=ROWS+HID)return true;
    if(by>=0&&bd[by][bx])return true;
  }
  return false;
}
function spawn(t){
  t=t||bag.shift();
  if(bag.length<7)refill(bag);
  cur={t,m:SHAPES[t].m.map(r=>r.slice()),r:0,x:t=='O'?4:3,y:0};
  lockT=0;resets=0;tspinFlag=false;gravAcc=0;spawnT=0;
  if(collide(board,cur.m,cur.x,cur.y))gameOver();
}
function startMode(m){
  mode=m;
  board=Array.from({length:ROWS+HID},()=>Array(COLS).fill(0));
  bag=[];refill(bag);
  hold=null;canHold=true;
  lines=0;score=0;level=1;combo=-1;b2b=0;pieces=0;time=0;
  flashes=[];popups=[];lands=[];drops=[];shines=[];
  quitHold=0; // fresh run never inherits a stale quit fill
  spawn();state='play';goPlay();
}
function grounded(){return collide(board,cur.m,cur.x,cur.y+1);}
function tryMove(dx,dy){
  if(collide(board,cur.m,cur.x+dx,cur.y+dy))return false;
  cur.x+=dx;cur.y+=dy;
  if(dx)tspinFlag=false;
  if(dy)lockT=0;
  else if(grounded()&&resets<MAX_RESETS){lockT=0;resets++;}
  return true;
}
function rotate(dir){
  if(cur.t=='O')return;
  const nm=rotateM(cur.m,dir),to=(cur.r+dir+4)%4;
  const kicks=(cur.t=='I'?KI:KJ)[''+cur.r+to];
  for(const[dx,dy]of kicks){
    if(!collide(board,nm,cur.x+dx,cur.y-dy)){
      cur.m=nm;cur.x+=dx;cur.y-=dy;cur.r=to;tspinFlag=true;
      if(grounded()&&resets<MAX_RESETS){lockT=0;resets++;}
      beep(440,0.03,'square',0.02);
      return;
    }
  }
}
function hardDrop(){
  let d=0;
  const sy=cur.y;
  while(!collide(board,cur.m,cur.x,cur.y+1)){cur.y++;d++;}
  score+=d*2;
  if(d)drops.push({m:cur.m,x:cur.x,sy,dy:cur.y-sy,t:0});
  const cs=[]; // ponytail: snapshot for the hard-drop white shine, lock() respawns cur
  for(let my=0;my<cur.m.length;my++)for(let mx=0;mx<cur.m[my].length;mx++)if(cur.m[my][mx])cs.push({x:cur.x+mx,y:cur.y+my});
  shines.push({cells:cs,t:0});
  lock();
}
function doHold(){
  if(!canHold)return;
  beep(330,0.05);
  const t=hold;hold=cur.t;
  if(t)spawn(t);else spawn();
  canHold=false;
}
function isTSpin(){
  const cx=cur.x+1,cy=cur.y+1;let n=0;
  for(const[dx,dy]of[[-1,-1],[1,-1],[-1,1],[1,1]]){
    const bx=cx+dx,by=cy+dy;
    if(bx<0||bx>=COLS||by<0||by>=ROWS+HID||board[by][bx])n++;
  }
  return n>=3;
}
function lock(){
  const ts=cur.t=='T'&&tspinFlag&&isTSpin();
  let above=true;
  for(let y=0;y<cur.m.length;y++)for(let x=0;x<cur.m[y].length;x++){
    if(!cur.m[y][x])continue;
    const by=cur.y+y;
    if(by>=HID)above=false;
    if(by>=0)board[by][cur.x+x]=cur.t;
    if(by>=HID)lands.push({x:cur.x+x,y:by,t:0});
  }
  pieces++;
  beep(180,0.04,'square',0.03);
  if(above){
    if(mode=='zen'){ // ponytail: zen clears the top 10 rows instead of ending the run
      board.splice(0,10);
      while(board.length<ROWS+HID)board.push(Array(COLS).fill(0));
      canHold=true;spawn();return;
    }
    return gameOver();
  }
  const cleared=[];
  for(let y=0;y<ROWS+HID;y++)if(board[y].every(c=>c))cleared.push(y);
  const n=cleared.length;
  let atk=0;
  if(n){
    for(const r of cleared)flashes.push({row:r,t:0});
    board=board.filter((_,i)=>!cleared.includes(i));
    while(board.length<ROWS+HID)board.unshift(Array(COLS).fill(0));
    const eligible=n==4||ts;
    combo++;
    atk=(ts?ATK.ts:ATK.n)[n-1]+CMB[Math.min(combo,7)]+(eligible&&b2b>0?1:0);
    if(mode=='ultra'){
      score+=atk*100; // blitz scoring: attack is the points
    }else{
      let base=ts?[400,800,1200,1600][n]:[0,100,300,500,800][n];
      if(eligible&&b2b>0)base=Math.floor(base*1.5);
      score+=(base+(combo>0?50*combo:0))*level;
    }
    b2b=eligible?b2b+1:0;
    lines+=n;
    let txt=ts?'T-SPIN'+['',' SINGLE',' DOUBLE',' TRIPLE'][n]:['','SINGLE','DOUBLE','TRIPLE','TETRIS'][n];
    if(eligible&&b2b>1)txt='B2B '+txt;
    if(ACTTX!='OFF')popups.push({txt,t:0});
    if(ACTTX=='ALL'&&combo>0)popups.push({txt:combo+' COMBO',t:0,small:1});
    if(ACTTX=='ALL'&&mode=='versus'&&atk)popups.push({txt:'+'+atk+' ATK',t:0,small:1});
    beep(n==4||ts?880:520,0.12,'square',0.05);
  }else combo=-1; // guideline: combo resets on a non-clearing lock
  if(mode=='versus'&&vs){
    const a=vsResolve(atk,vs.pIn);
    if(a>0)vs.bIn.push(a);
    let g=0;while(vs.pIn.length)g+=vs.pIn.shift();
    if(g){addGarbage(g);beep(90,0.15,'sawtooth',0.05);if(state!='play')return;}
  }
  if(mode=='marathon'||mode=='zen')level=Math.min(15,1+(lines/10|0));
  const md=MODES[mode];
  if(md&&md.goal&&lines>=md.goal)return finish();
  canHold=true;
  spawn();
}
function gravity(){
  if(mode=='marathon'||mode=='zen')return Math.pow(0.8-(level-1)*0.007,level-1)*1000;
  return 1000; // sprint/ultra: 1G, jstris-style
}
function finish(){state='over';saveBest();beep(660,0.2);beep(990,0.3);}
function gameOver(){state='over';saveBest();beep(220,0.3,'sawtooth',0.05);}
function saveBest(){
  if(mode=='versus')return;
  const lower=mode=='sprint',r=lower?time:score;
  if(!best[mode]||(lower?r<best[mode]:r>best[mode]))best[mode]=r;
   lsSet('webtris_best',best);
}
function fmtTime(ms){
  const m=ms/60000|0,s=(ms/1000|0)%60,c=(ms/10|0)%100;
  return m+':'+String(s).padStart(2,'0')+'.'+String(c).padStart(2,'0');
}

function update(dt){
  if(state!='play')return;
  // ponytail: holding quit fills the bar while the run continues, no pause
  if(keys[keybinds.quit]){quitHold+=dt;if(quitHold>=QUIT_HOLD){saveBest();goMenu();quitHold=0;return;}}
  time+=dt;
  if(mode=='ultra'&&time>=MODES.ultra.time)return finish();
  if(mode=='versus'&&vs){
    botUpdate(vs.bot,dt);
    if(vs.bot.dead){vs.win=true;state='over';beep(660,0.2);beep(990,0.3);return;}  }
  // DAS/ARR
  if(moveDir){
    dasT+=dt;
    if(dasT>=DAS){arrT+=dt;while(arrT>=ARR){tryMove(moveDir,0);arrT-=ARR;}}
  }
  // gravity / soft drop
  const soft=keys[keybinds.softDrop];
  const iv=soft?Math.min(gravity(),SOFT):gravity();
  if(prevIv&&iv!=prevIv)gravAcc*=iv/prevIv; // keep position continuous, no jump on speed change
  prevIv=iv;
  gravAcc+=dt;
  let guard=ROWS+HID;
  while(gravAcc>=iv&&guard--){
    gravAcc-=iv;
    if(tryMove(0,1)&&soft)score+=1;
  }
  if(grounded()){
    lockT+=dt;
    if(lockT>=LOCK_DELAY)lock();
  }
  function age(list,ttl){list.forEach(e=>e.t+=dt);return list.filter(e=>e.t<ttl);}
  flashes=age(flashes,160);lands=age(lands,150);drops=age(drops,70);shines=age(shines,260);
  if(reducedMotion){flashes=[];lands=[];drops=[];shines=[];}
  spawnT+=dt;
  popups=age(popups,900);
}

// --- rendering ---
function block(x,y,size,color,alpha=1){
  // ponytail: glossy mino — dark edge, flat base, white top shine, dark bottom; no roundRect
  ctx.globalAlpha=alpha;
  ctx.fillStyle='rgba(0,0,0,0.5)';ctx.fillRect(x,y,size,size);
  ctx.fillStyle=color;ctx.fillRect(x+1,y+1,size-2,size-2);
  const ix=Math.max(2,size*0.09),iw=size-ix*2;
  ctx.fillStyle='rgba(255,255,255,0.30)';ctx.fillRect(x+ix,y+ix,iw,iw*0.42);
  ctx.fillStyle='rgba(0,0,0,0.22)';ctx.fillRect(x+ix,y+size-ix-iw*0.26,iw,iw*0.26);
  ctx.globalAlpha=1;
}
function cell(px,py,color,alpha=1){block(BX+px*CELL,BY+(py-HID)*CELL,CELL,color,alpha);}
function sideBox(x,y,w,h,cut,corner){ // ponytail: attached box with one chamfered outer corner
  ctx.beginPath();
  if(corner=='bl'){ctx.moveTo(x,y);ctx.lineTo(x+w,y);ctx.lineTo(x+w,y+h);ctx.lineTo(x+cut,y+h);ctx.lineTo(x,y+h-cut);}
  else{ctx.moveTo(x,y);ctx.lineTo(x+w,y);ctx.lineTo(x+w,y+h-cut);ctx.lineTo(x+w-cut,y+h);ctx.lineTo(x,y+h);}
  ctx.closePath();
  ctx.fillStyle='rgba(0,0,0,0.80)';ctx.fill();
  ctx.lineWidth=2;ctx.strokeStyle='#e8ebf5';ctx.stroke();
  ctx.fillStyle='#e8ebf5';ctx.fillRect(x,y,w,24);
}
function mini(t,cx,cy,size,alpha=1){
  const m=SHAPES[t].m,n=m.length,ox=cx-n*size/2,oy=cy-n*size/2;
  for(let y=0;y<n;y++)for(let x=0;x<n;x++)if(m[y][x])block(ox+x*size,oy+y*size,size,SHAPES[t].c,alpha);
}
function text(str,x,y,size=14,color='#cfd3e0',align='left'){
  ctx.font='700 '+size+'px "Space Grotesk",ui-monospace,monospace';
  ctx.letterSpacing='1px'; // unsupported browsers keep it as a harmless expando
  ctx.fillStyle=color;ctx.textAlign=align;ctx.fillText(str,x,y);
  ctx.letterSpacing='0px';
}
function hexA(h,a){ // ponytail: #rrggbb + alpha for the colored ghost, no color lib
  const p=[1,3,5].map(i=>parseInt(h.slice(i,i+2),16));
  return 'rgba('+p[0]+','+p[1]+','+p[2]+','+a+')';
}
function hexMix(a,b,t){ // ponytail: 2-hex lerp for tetr.io pastel titles, no color lib
  const p=h=>[1,3,5].map(i=>parseInt(h.slice(i,i+2),16));
  const A=p(a),B=p(b);
  return '#'+A.map((v,i)=>Math.round(v+(B[i]-v)*t).toString(16).padStart(2,'0')).join('');
}
function panel(x,y,w,h){
  ctx.fillStyle='#14161f';ctx.fillRect(x,y,w,h);
  ctx.fillStyle='rgba(255,255,255,0.03)';ctx.fillRect(x,y,w,2);
  ctx.strokeStyle='#2a2e3f';ctx.strokeRect(x+.5,y+.5,w-1,h-1);
}
function button(x,y,w,h,label,fn){
  const hover=mouseX>=x&&mouseX<x+w&&mouseY>=y&&mouseY<y+h;
  panel(x,y,w,h);
  if(hover){
    ctx.fillStyle='rgba(143,163,255,0.08)';ctx.fillRect(x,y,w,h);
    ctx.strokeStyle='#8fa3ff';ctx.strokeRect(x+.5,y+.5,w-1,h-1);
  }
  text(label,x+w/2,y+h/2+5,13,hover?'#e8ebf5':'#8fa3ff','center');
  clickZones.push({x,y,w,h,fn});
}
function draw(){
  // ponytail: cursor based on last frame's clickZones (1-frame lag, invisible); avoids per-state duplication
  const over=clickZones.some(z=>mouseX>=z.x&&mouseX<z.x+z.w&&mouseY>=z.y&&mouseY<z.y+z.h);
  cvs.style.cursor=over?'pointer':'default';
  ctx.clearRect(0,0,cvs.width,cvs.height); // ponytail: transparent so body wallpaper photo shows
  // ponytail: no blanket darken in play mode — board & HUD panels paint their own opaque bg, so the wallpaper reads full-screen behind them (over draws its own scrim)
  clickZones=[];
  if(mode=='versus'){CELL=20;BX=30;BY=40;}else{CELL=30;BX=150;BY=30;}
  if(state=='play'&&quitHold>0)drawQuitBar();else hideQuitBar(); // before the menu/config/diff early returns
  if(state=='menu'){drawMenu();return;}
  if(state=='config'){drawConfig();return;}
  if(state=='diff'){drawDiff();return;}
  // ponytail: cursor set once at end of draw() based on clickZones, not per-state
  // board
  ctx.fillStyle='rgba(0,0,0,'+(BGV/100)+')';ctx.fillRect(BX,BY,COLS*CELL,ROWS*CELL);
  ctx.lineWidth=1;ctx.strokeStyle='rgba(255,255,255,'+(GRIDV/100)+')';
  for(let x=1;x<COLS;x++){ctx.beginPath();ctx.moveTo(BX+x*CELL,BY);ctx.lineTo(BX+x*CELL,BY+ROWS*CELL);ctx.stroke();}
  for(let y=1;y<ROWS;y++){ctx.beginPath();ctx.moveTo(BX,BY+y*CELL);ctx.lineTo(BX+COLS*CELL,BY+y*CELL);ctx.stroke();}
  ctx.lineWidth=2;ctx.strokeStyle='#e8ebf5';ctx.strokeRect(BX-1,BY-1,COLS*CELL+2,ROWS*CELL+2);
  for(let y=HID;y<ROWS+HID;y++)for(let x=0;x<COLS;x++)if(board[y][x])cell(x,y,SHAPES[board[y][x]].c);
  for(const l of lands){
    const a=1-l.t/150;
    ctx.fillStyle='rgba(255,255,255,'+(a*0.5)+')';
    ctx.fillRect(BX+l.x*CELL,BY+(l.y-HID)*CELL,CELL,CELL);
  }
  for(const f of flashes){
    const a=1-f.t/160;
    ctx.fillStyle='rgba(255,255,255,'+(a*0.8)+')';
    ctx.fillRect(BX,BY+(f.row-HID)*CELL,COLS*CELL,CELL);
  }
  if(cur&&state=='play'){
    ctx.save();ctx.beginPath();ctx.rect(BX,BY,COLS*CELL,ROWS*CELL);ctx.clip(); // slide in from top edge
    for(const dr of drops){ // hard-drop trail: white piece sliding down, 100ms
      const p=dr.t/70,y=dr.sy+dr.dy*p;
      for(let my=0;my<dr.m.length;my++)for(let mx=0;mx<dr.m[my].length;mx++)
        if(dr.m[my][mx])cell(dr.x+mx,y+my,'#ffffff',0.9*(1-p));
    }
    if(SHADV>0){let gy=cur.y;while(!collide(board,cur.m,cur.x,gy+1))gy++;
    ctx.lineWidth=2; // ponytail: ghost style computed once, not per cell
    ctx.strokeStyle=COLORGHOST?hexA(SHAPES[cur.t].c,SHADV/100):'rgba(255,255,255,'+SHADV/100+')';
    for(let y=0;y<cur.m.length;y++)for(let x=0;x<cur.m[y].length;x++)
      if(cur.m[y][x]&&gy+y>=HID)ctx.strokeRect(BX+(cur.x+x)*CELL+2,BY+(gy+y-HID)*CELL+2,CELL-4,CELL-4);}
    // smooth fall: fractional offset from gravity progress; 0 when landed
    const iv=keys[keybinds.softDrop]?Math.min(gravity(),SOFT):gravity();
    const off=grounded()?0:Math.min(gravAcc/iv,1);
    const fa=Math.min(1,spawnT/120); // spawn fade-in
    for(let y=0;y<cur.m.length;y++)for(let x=0;x<cur.m[y].length;x++)
      if(cur.m[y][x])cell(cur.x+x,cur.y+off+y,SHAPES[cur.t].c,fa);
    ctx.restore();
    ctx.save();ctx.beginPath();ctx.rect(BX,BY,COLS*CELL,ROWS*CELL);ctx.clip(); // hard-drop white shine
    for(const s of shines){
      const a=1-s.t/260;
      ctx.save();ctx.shadowColor='rgba(255,255,255,'+(0.9*a)+')';ctx.shadowBlur=18;
      ctx.fillStyle='rgba(255,255,255,'+(0.85*a)+')';
      for(const c of s.cells)ctx.fillRect(BX+c.x*CELL,BY+(c.y-HID)*CELL,CELL,CELL);
      ctx.restore();
    }
    ctx.restore();
  }
  if(mode=='versus'&&vs){
    // compact HUD in the middle strip between the two boards
    panel(250,40,100,64);text('HOLD',258,58,10,'#6b7288');
    if(hold)mini(hold,300,82,10,(!GRAYHOLD||canHold)?1:0.3);
    panel(250,118,100,180);text('NEXT',258,136,10,'#6b7288');
    for(let i=0;i<3&&i<bag.length;i++)mini(bag[i],300,168+i*52,10);
    panel(250,312,100,58);text('TIME',258,330,10,'#6b7288');text(fmtTime(time),258,354,14);
    text('YOU',BX+COLS*CELL/2,30,12,'#6b7288','center');
    text('CPU - '+DIFFS[vs.diff-1].name,370+COLS*CELL/2,30,12,'#6b7288','center');
    meter(BX+COLS*CELL+4,vs.pIn.reduce((a,b)=>a+b,0));
    meter(360,vs.bIn.reduce((a,b)=>a+b,0));
    drawBot(vs.bot);
  }else{
    // ponytail: HOLD/NEXT boxes attached to the board, stats as bare text on the wallpaper
    const hw=110,hh=110,nx=BX+COLS*CELL,nh=ROWS*CELL;
    sideBox(BX-hw,BY,hw,hh,12,'bl');
    text('HOLD',BX-hw+8,BY+17,13,'#0a0c12');
    if(hold)mini(hold,BX-hw/2,BY+72,14,(!GRAYHOLD||canHold)?1:0.3);
    sideBox(nx,BY,hw,nh,12,'br');
    text('NEXT',nx+8,BY+17,13,'#0a0c12');
    for(let i=0;i<5&&i<bag.length;i++)mini(bag[i],nx+hw/2,BY+74+i*62,12);
    text('SCORE',nx+12,BY+nh-52,11,'#cfd3e0');
    text(''+score,nx+12,BY+nh-16,30,'#ffffff');
    let sy=BY+hh+52; // bare stats under HOLD, right-aligned to the board
    function lstat(label,val,vs=26){text(label,BX-14,sy,11,'#cfd3e0','right');text(val,BX-14,sy+28,vs,'#ffffff','right');sy+=62;}
    if(mode=='sprint'){lstat('LINES',lines+'/40');lstat('TIME',fmtTime(time),20);}
    else if(mode=='ultra'){lstat('TIME LEFT',fmtTime(Math.max(0,120000-time)),20);} // ponytail: SCORE already lives in the NEXT box
    else{lstat('LEVEL',''+level);lstat('LINES',mode=='zen'?''+lines:lines+'/150');lstat('TIME',fmtTime(time),20);}
  }
  // popups
  let py=260;
  for(const p of popups){
    const a=1-p.t/900;
    ctx.globalAlpha=a;
    text(p.txt,BX+COLS*CELL/2,reducedMotion?py:py-p.t/20,p.small?14:20,p.small?'#8fa3ff':'#ffd75e','center');
    ctx.globalAlpha=1;
    py+=p.small?22:30;
  }
  if(state=='over')drawOver();
}
const GLYPH={
  A:['.##.','#..#','####','#..#','#..#'],B:['###.','#..#','###.','#..#','###.'],
  C:['.###','#...','#...','#...','.###'],E:['####','#...','###.','#...','####'],
  F:['####','#...','###.','#...','#...'],G:['.###','#...','#.##','#..#','.###'],
  L:['#...','#...','#...','#...','####'],
  M:['##.##','#.#.#','#.#.#','#...#','#...#'],P:['###.','#..#','###.','#...','#...'],
  S:['.###','#...','.##.','...#','###.'],T:['#####','..#..','..#..','..#..','..#..'],
  V:['#...#','#...#','#...#','.#.#.','..#..'],
  Z:['####','...#','.##.','#...','####'],
};
function glyphIcon(str,x,y,s,color,bx,by,bw,bh){
  const SH=Math.round(bh*0.9); // ponytail: one solid extrusion per cell, no stepped copies
  ctx.save();ctx.beginPath();ctx.rect(bx,by,bw,bh);ctx.clip();
  ctx.fillStyle='rgba(0,0,0,0.45)';
  ctx.beginPath();
  let sx=x;
  for(const ch of str){
    const g=GLYPH[ch];
    if(g)for(let r=0;r<5;r++)for(let c=0;c<g[r].length;c++)if(g[r][c]=='#'){
      const px=sx+c*s,py=y+r*s;
      ctx.moveTo(px,py);ctx.lineTo(px+s,py);ctx.lineTo(px+s+SH,py+SH);
      ctx.lineTo(px+s+SH,py+s+SH);ctx.lineTo(px+SH,py+s+SH);ctx.lineTo(px,py+s);ctx.closePath();
    }
    sx+=(g?g[0].length:4)*s+s;
  }
  ctx.fill();
  ctx.restore();
  let cx=x;
  [...str].forEach((ch,idx)=>{
    const g=GLYPH[ch],c0=idx==0?hexMix(color,'#ffffff',0.18):color; // ponytail: first letter lighter, like MP/CFG
    if(g){
      ctx.fillStyle=c0;
      for(let r=0;r<5;r++)for(let c=0;c<g[r].length;c++)if(g[r][c]=='#')ctx.fillRect(cx+c*s,y+r*s,s,s);
      ctx.fillStyle='rgba(255,255,255,0.22)'; // lighter top cell per column
      for(let c=0;c<g[0].length;c++)for(let r=0;r<5;r++)if(g[r][c]=='#'){ctx.fillRect(cx+c*s,y+r*s,s,Math.max(2,s*0.32));break;}
    }
    cx+=(g?g[0].length:4)*s+s;
  });
  return cx-s-x; // width drawn
}
function drawMenu(){
  // tetr.io home: top chrome, full-width tinted bars, bottom status bar
  const rows=[
    ...Object.entries(MODES).map(([m,md],i)=>({key:m,md,icon:['SP','BL','MA','ZE','VS'][i],fn:()=>m=='versus'?(goPlay(),state='diff'):startMode(m)})),
    {key:'cfg',md:{label:'SETTINGS',sub:'handling & keybindings',accent:'#8fa3ff'},icon:'CF',fn:()=>{cvs.width=innerWidth;cvs.height=innerHeight;state='config';}},
  ];
  const W=cvs.width,H=cvs.height;
  const TOP=60,BOT=34,gap=12,n=rows.length;
  const rh=Math.max(56,Math.min(84,H*0.09)),rx=Math.max(180,W*0.20),rw=W-rx;
  const y0=TOP+12;
  const x0=rx-40; // ponytail: hovered row extends left into the photo
  ctx.fillStyle='rgba(7,8,13,0.55)';ctx.fillRect(0,0,W,H); // even scrim so bars read
  rows.forEach((r,i)=>{
    const y=y0+i*(rh+gap);
    const hoverTarget=mouseX>=x0&&mouseX<W&&mouseY>=y&&mouseY<y+rh?1:0;
    menuHover[i]=reducedMotion?hoverTarget:menuHover[i]+(hoverTarget-menuHover[i])*0.18;
    const t=menuHover[i];
    const xt=rx-t*40,bw=rw+t*40;
    ctx.save();
    ctx.shadowColor='rgba(0,0,0,0.6)';ctx.shadowBlur=16; // ponytail: small centered soft glow, no offset
    ctx.fillStyle='#10121a';ctx.fillRect(xt,y,bw,rh);
    ctx.restore();
    ctx.globalAlpha=0.22+0.18*t;
    ctx.fillStyle=r.md.accent;ctx.fillRect(xt,y,bw,rh);
    ctx.globalAlpha=1;
    ctx.fillStyle='rgba(255,255,255,0.08)';ctx.fillRect(xt,y,bw,rh*0.07); // ponytail: hard top light band, no gradient
    ctx.fillStyle='rgba(0,0,0,0.35)';ctx.fillRect(xt,y+rh*0.93,bw,rh*0.07); // hard bottom dark band
    ctx.fillStyle='rgba(255,255,255,0.07)';ctx.fillRect(xt,y,bw,2); // top highlight
    ctx.fillStyle='rgba(0,0,0,0.5)';ctx.fillRect(xt,y+rh-4,bw,4); // bottom shade
    ctx.strokeStyle='rgba(0,0,0,0.6)';ctx.lineWidth=1;ctx.strokeRect(xt+.5,y+.5,bw-1,rh-1); // ponytail: static outline, no hover color change
    const gs=Math.max(7,Math.min(20,rh*0.14)); // ponytail: glyph height ~70% of bar, like tetr.io
    const gw=glyphIcon(r.icon,xt+28,y+(rh-5*gs)/2,gs,r.md.accent,xt,y,bw,rh);
    const title=hexMix(r.md.accent,'#ffffff',0.35+0.4*t);
    const sub=hexMix(r.md.accent,'#8a90a5',0.45);
    text(r.md.label,xt+30+gw+18,y+rh/2-2,Math.max(20,rh*0.28),title);
    text(r.md.sub.toUpperCase(),xt+30+gw+18,y+rh/2+20,11,sub);
    if(best[r.key]){
      const b=r.key=='sprint'?fmtTime(best[r.key]):best[r.key];
      text('BEST  '+b,xt+bw-18,y+rh-12,10,'rgba(255,255,255,0.55)','right');
    }
    clickZones.push({x:xt,y,w:bw,h:rh,fn:r.fn});
  });
  // top chrome
  ctx.fillStyle='#14161f';ctx.fillRect(0,0,W,TOP);
  ctx.fillStyle='rgba(255,255,255,0.06)';ctx.fillRect(0,0,W,2);
  ctx.fillStyle='#2a2e3f';ctx.fillRect(0,TOP-2,W,2);
  text('HOME',20,TOP/2+6,22,'#9aa1b5');
  // bottom chrome
  ctx.fillStyle='#14161f';ctx.fillRect(0,H-BOT,W,BOT);
  ctx.fillStyle='#2a2e3f';ctx.fillRect(0,H-BOT,W,2);
  text('WELCOME TO WEBTRIS!',20,H-BOT/2+5,13,'#9aa1b5');
  text('TETR.IO-INSPIRED THEME',W-16,H-BOT/2+5,10,'#6b7288','right');
  text('WEBTRIS',24,H-BOT-24,15,'rgba(232,235,245,0.28)');
}
function drawDiff(){
  text('VS AI',300,90,44,'#e8ebf5','center');
  ctx.fillStyle='#ef4a4a';ctx.fillRect(264,108,72,3);
  text('pick a difficulty',300,128,12,'#6b7288','center');
  const accents=['#3ecf4a','#7fd44a','#ffd75e','#f7941e','#ef4a4a'];
  DIFFS.forEach((d,i)=>{
    const y=170+i*72;
    const hover=mouseX>=150&&mouseX<450&&mouseY>=y&&mouseY<y+56;
    ctx.fillStyle=hover?'rgba(40,46,68,0.85)':'rgba(16,19,29,0.82)';ctx.fillRect(150,y,300,56);
    ctx.fillStyle=accents[i];ctx.fillRect(150,y,4,56);
    ctx.strokeStyle=hover?accents[i]:'rgba(60,68,100,0.9)';ctx.strokeRect(150.5,y+.5,299,55);
    text('['+(i+1)+']',166,y+24,11,'#6b7288');
    text(d.name,196,y+34,18,hover?accents[i]:'#e8ebf5');
    clickZones.push({x:150,y,w:300,h:56,fn:()=>startVs(i+1)});
  });
  text('esc - back',300,628,11,'#6b7288','center');
}
function drawConfig(){
  const W=cvs.width,cx=W/2,mx=10,bw=W-mx*2,BH=58,GAP=10;
  ctx.fillStyle='rgba(5,6,10,0.55)';ctx.fillRect(0,0,W,cvs.height); // dim so bars pop, wallpaper still reads
  text('HOVER OVER A SETTING FOR MORE INFO',cx,26,12,'#6b7288','center');
  { // ponytail: BACK is a grey menu bar pinned to the left edge, extends right on hover
    const bw2=170,bh2=30,by=6,acc='#9aa1b5';
    const hov=mouseX>=0&&mouseX<bw2+40&&mouseY>=by&&mouseY<by+bh2;
    const hoverTarget=hov?1:0;
    backHover=reducedMotion?hoverTarget:backHover+(hoverTarget-backHover)*0.18;
    const t=backHover,bwH=bw2+t*40;
    ctx.save();
    ctx.shadowColor='rgba(0,0,0,0.6)';ctx.shadowBlur=16;
    ctx.fillStyle='#10121a';ctx.fillRect(0,by,bwH,bh2);
    ctx.restore();
    ctx.globalAlpha=0.22+0.18*t;ctx.fillStyle=acc;ctx.fillRect(0,by,bwH,bh2);ctx.globalAlpha=1;
    ctx.fillStyle='rgba(255,255,255,0.08)';ctx.fillRect(0,by,bwH,bh2*0.07);
    ctx.fillStyle='rgba(0,0,0,0.35)';ctx.fillRect(0,by+bh2*0.93,bwH,bh2*0.07);
    ctx.strokeStyle='rgba(0,0,0,0.6)';ctx.strokeRect(0.5,by+.5,bwH-1,bh2-1);
    text('BACK',16,by+bh2/2+5,15,hexMix(acc,'#ffffff',0.35+0.4*t));
    clickZones.push({x:0,y:by,w:bwH,h:bh2,fn:()=>goMenu()});
  }
  const short=k=>{const m={'ArrowLeft':'Left','ArrowRight':'Right','ArrowDown':'Down','ArrowUp':'Up','ShiftLeft':'L-Shift','ShiftRight':'R-Shift','Escape':'Esc',Space:'Space'};return m[k]||k.replace(/^(Key|Digit)/,'');};
  const checkRow=(x,y,w,l,on,fn)=>{ // tetr.io-style checkbox row, no box chrome
    ctx.fillStyle=on?'#8fa3ff':'rgba(5,7,12,0.9)';ctx.fillRect(x,y+5,22,22);
    ctx.strokeStyle=on?'#8fa3ff':'#4a5170';ctx.strokeRect(x+.5,y+5.5,21,21);
    ctx.fillStyle='rgba(255,255,255,0.12)';ctx.fillRect(x+1,y+6,20,2); // top light edge
    if(on){ctx.strokeStyle='#0b0e18';ctx.lineWidth=3;ctx.beginPath();
      ctx.moveTo(x+5,y+16);ctx.lineTo(x+10,y+21);ctx.lineTo(x+18,y+10);ctx.stroke();ctx.lineWidth=1;}
    text(l,x+32,y+22,15,on?'#aab2cf':'#5b6280');
    clickZones.push({x,y,w,h:32,fn});
  };
  const segCtrl=(x,y,w,l,opts,cur,fn)=>{ // label + OFF/HOLD/TAP-style segmented row
    text(l,x+8,y+16,13,'#8f97b5');
    const sw=(w-16-(opts.length-1)*6)/opts.length;
    opts.forEach((o,i)=>{
      const bx=x+8+i*(sw+6),sel=cur==o;
      const ph=mouseX>=bx&&mouseX<bx+sw&&mouseY>=y+24&&mouseY<y+54;
      shadeBar(bx,y+24,sw,30,'#8fa3ff',(sel||ph)?1:0);
      text(o,bx+sw/2,y+45,14,sel?'#dfe4f5':'#6f7794','center');
      if(!sel)clickZones.push({x:bx,y:y+24,w:sw,h:30,fn:()=>fn(o)});
    });
  };
  const CTRL_LABEL={left:'MOVE FALLING PIECE LEFT',right:'MOVE FALLING PIECE RIGHT',softDrop:'SOFT DROP',hardDrop:'HARD DROP',rotCCW:'ROTATE COUNTERCLOCKWISE',rotCW:'ROTATE CLOCKWISE',hold:'SWAP HOLD PIECE',retry:'RETRY GAME',quit:'FORFEIT GAME'};
  const shadeBar=(x,y,w,h,acc,t)=>{ // main-menu bar shading for inner controls
    ctx.fillStyle='#10121a';ctx.fillRect(x,y,w,h);
    ctx.globalAlpha=0.22+0.18*t;ctx.fillStyle=acc;ctx.fillRect(x,y,w,h);ctx.globalAlpha=1;
    ctx.fillStyle='rgba(255,255,255,0.08)';ctx.fillRect(x,y,w,Math.max(2,h*0.07));
    ctx.fillStyle='rgba(0,0,0,0.35)';ctx.fillRect(x,y+h-Math.max(2,h*0.07),w,Math.max(2,h*0.07));
    ctx.fillStyle='rgba(255,255,255,0.07)';ctx.fillRect(x,y,w,2);
    ctx.fillStyle='rgba(0,0,0,0.5)';ctx.fillRect(x,y+h-Math.min(4,h*0.1),w,Math.min(4,h*0.1));
    ctx.strokeStyle='rgba(0,0,0,0.6)';ctx.lineWidth=1;ctx.strokeRect(x+.5,y+.5,w-1,h-1);
  };
  const slider=(x,y,w,r)=>{ // click-to-set track, no drag state needed
    const long=r.l.length>4,loff=long?210:110; // gameplay labels are full words
    const hov=mouseX>=x&&mouseX<x+w&&mouseY>=y&&mouseY<y+56;
    shadeBar(x,y+2,w,52,'#8fa3ff',hov?1:0);
    const tx0=x+loff,tx1=x+w-110,ty=y+18;
    text(r.l,x+8,y+26,long?14:20,'#8f97b5');
    ctx.fillStyle='rgba(0,0,0,0.4)';ctx.fillRect(tx0,ty,tx1-tx0,5); // track
    ctx.fillStyle='rgba(255,255,255,0.10)';ctx.fillRect(tx0,ty,tx1-tx0,1);
    const f=(r.g()-r.lo)/(r.hi-r.lo),kx=tx0+f*(tx1-tx0);
    ctx.fillStyle='#262b40';ctx.fillRect(kx-10,ty-10,20,25); // knob
    ctx.strokeStyle='#4a5170';ctx.strokeRect(kx-9.5,ty-9.5,19,24);
    text(r.loL||'SLOW',tx0,y+46,9,'#4b5266');
    text(r.hiL||'FAST',tx1,y+46,9,'#4b5266','right');
    shadeBar(x+w-96,y+8,88,30,'#8fa3ff',0); // value chip
    text(r.fmt(r.g()),x+w-52,y+29,14,'#e8ebf5','center');
    clickZones.push({x:tx0-10,y:y,w:tx1-tx0+20,h:40,fn:(cx)=>{
      let v=r.lo+Math.min(1,Math.max(0,(cx-tx0)/(tx1-tx0)))*(r.hi-r.lo);
      r.s(Math.min(r.hi,Math.max(r.lo,Math.round(v/r.st)*r.st)));r.save();
    }});
  };
  const body={
    controls(px,y,w){
      ctx.fillStyle='rgba(13,16,26,0.88)';ctx.fillRect(px-14,y-8,w+28,10*30+16); // content well
      let yy=y;
      for(const a of KEY_ACTIONS){
        const chipW=120,cx=px+w-chipW;
        const hover=mouseX>=cx&&mouseX<cx+chipW&&mouseY>=yy&&mouseY<yy+24;
        text(CTRL_LABEL[a.id],px+8,yy+18,15,rebindAction==a.id?'#ffd75e':'#8f97b5');
        if(rebindAction==a.id){ctx.fillStyle='rgba(60,58,40,0.9)';ctx.fillRect(cx,yy,chipW,24);}
        else shadeBar(cx,yy,chipW,24,'#8fa3ff',hover?1:0);
        if(rebindAction==a.id||hover){ctx.strokeStyle=rebindAction==a.id?'#ffd75e':'#8fa3ff';ctx.strokeRect(cx+.5,yy+.5,chipW-1,23);}
        text(rebindAction==a.id?'...':short(keybinds[a.id]).toUpperCase(),cx+chipW/2,yy+17,12,rebindAction==a.id?'#ffd75e':'#aab2cf','center');
        clickZones.push({x:cx,y:yy,w:chipW,h:24,fn:()=>{rebindAction=rebindAction==a.id?null:a.id;}});
        ctx.fillStyle='rgba(255,255,255,0.05)';ctx.fillRect(px,yy+27,w,1); // divider
        yy+=30;
      }
      return yy-y+4;
    },
    handling(px,y,w){
      ctx.fillStyle='rgba(13,16,26,0.88)';ctx.fillRect(px-14,y-8,w+28,38+3*56+12);
      button(px+w-110,y,100,30,'RESET',()=>{DAS=110;ARR=25;SOFT=100;saveHand();});
      const rows=[
        {l:'ARR',g:()=>ARR,s:v=>ARR=v,lo:5,hi:100,st:1,fmt:v=>v+'MS',save:saveHand},
        {l:'DAS',g:()=>DAS,s:v=>DAS=v,lo:30,hi:200,st:1,fmt:v=>v+'MS',save:saveHand},
        {l:'SDF',g:()=>SOFT,s:v=>SOFT=v,lo:0,hi:200,st:5,fmt:v=>v==0?'INST':v+'MS',save:saveHand},
      ];
      rows.forEach((r,i)=>slider(px,y+38+i*56,w,r));
      return 38+3*56+4;
    },
    volume(px,y,w){
      ctx.fillStyle='rgba(13,16,26,0.88)';ctx.fillRect(px-14,y-8,w+28,56+32+12); // content well
      slider(px,y,w,{l:'SFX',loL:'QUIET',hiL:'LOUD',g:()=>VOL,s:v=>VOL=v,lo:0,hi:100,st:1,fmt:v=>v+'%',save:()=>{lsSet('webtris_vol',VOL);beep(660);}});
      checkRow(px,y+56,w,'DISABLE SOUND ENTIRELY',MUTE,()=>{MUTE=!MUTE;lsSet('webtris_mute',MUTE);});
      return 56+32+12;
    },
    gameplay(px,y,w){
      ctx.fillStyle='rgba(13,16,26,0.88)';ctx.fillRect(px-14,y-8,w+28,64+3*56+2*32+12);
      segCtrl(px,y,w,'ACTION TEXT',['OFF','SOME','ALL'],ACTTX,v=>{ACTTX=v;saveGp();});
      slider(px,y+64,w,{l:'GRID VISIBILITY',loL:'TRANSPARENT',hiL:'OPAQUE',g:()=>GRIDV,s:v=>GRIDV=v,lo:0,hi:100,st:1,fmt:v=>v+'%',save:saveGp});
      slider(px,y+120,w,{l:'BOARD VISIBILITY',loL:'TRANSPARENT',hiL:'OPAQUE',g:()=>BGV,s:v=>BGV=v,lo:0,hi:100,st:1,fmt:v=>v+'%',save:saveGp});
      slider(px,y+176,w,{l:'SHADOW VISIBILITY',loL:'TRANSPARENT',hiL:'OPAQUE',g:()=>SHADV,s:v=>SHADV=v,lo:0,hi:100,st:1,fmt:v=>v+'%',save:saveGp});
      checkRow(px,y+232,w,'COLORED SHADOW PIECE',COLORGHOST,()=>{COLORGHOST=!COLORGHOST;saveGp();});
      checkRow(px,y+264,w,'GRAY OUT LOCKED HOLD PIECE',GRAYHOLD,()=>{GRAYHOLD=!GRAYHOLD;saveGp();});
      return 64+3*56+2*32+12;
    },
  };
  const SECS=[
    {id:'controls',label:'CONTROLS'},{id:'handling',label:'HANDLING'},
    {id:'volume',label:'VOLUME & AUDIO'},{id:'gameplay',label:'GAMEPLAY'},
  ];
  let y=44;
  for(const s of SECS){
    const open=openSec==s.id;
    const hover=mouseX>=mx&&mouseX<mx+bw&&mouseY>=y&&mouseY<y+BH;
    ctx.save(); // ponytail: section bars share the main menu bar shading
    ctx.shadowColor='rgba(0,0,0,0.6)';ctx.shadowBlur=16;
    ctx.fillStyle='#10121a';ctx.fillRect(mx,y,bw,BH);
    ctx.restore();
    ctx.globalAlpha=open?0.40:hover?0.30:0.22;
    ctx.fillStyle='#8fa3ff';ctx.fillRect(mx,y,bw,BH);
    ctx.globalAlpha=1;
    ctx.fillStyle='rgba(255,255,255,0.08)';ctx.fillRect(mx,y,bw,BH*0.07); // hard top light band
    ctx.fillStyle='rgba(0,0,0,0.35)';ctx.fillRect(mx,y+BH*0.93,bw,BH*0.07); // hard bottom dark band
    ctx.fillStyle='rgba(255,255,255,0.07)';ctx.fillRect(mx,y,bw,2); // top highlight
    ctx.fillStyle='rgba(0,0,0,0.5)';ctx.fillRect(mx,y+BH-4,bw,4); // bottom shade
    ctx.strokeStyle='rgba(0,0,0,0.6)';ctx.lineWidth=1;ctx.strokeRect(mx+.5,y+.5,bw-1,BH-1);
    ctx.fillStyle='rgba(0,0,0,0.35)';ctx.fillRect(mx+10,y+7,44,44); // chevron box
    ctx.fillStyle=open?'#c3c9e0':'#7c86a3'; // chevron triangle, no glyph dependency
    const tx=mx+32,ty=y+BH/2+(open?-3:2);
    ctx.beginPath();
    if(open){ctx.moveTo(tx-9,ty+5);ctx.lineTo(tx+9,ty+5);ctx.lineTo(tx,ty-5);}
    else{ctx.moveTo(tx-9,ty-5);ctx.lineTo(tx+9,ty-5);ctx.lineTo(tx,ty+5);}
    ctx.closePath();ctx.fill();
    text(s.label,mx+66,y+BH/2+11,30,open?'#c3c9e0':hover?'#aab2cf':'#8f97b5');
    clickZones.push({x:mx,y,w:bw,h:BH,fn:()=>{openSec=open?null:s.id;}});
    y+=BH+GAP;
    if(open){
      const ph=body[s.id](mx+14,y+8,bw-28);
      y+=ph+8;
    }
  }
  text('esc - back',cx,y+22,12,'#6b7288','center');
  clickZones.push({x:cx-60,y:y+4,w:120,h:30,fn:()=>goMenu()});
}
function saveHand(){lsSet('webtris_handling',{das:DAS,arr:ARR,soft:SOFT});}
// --- versus helpers ---
function startVs(diff){
  startMode('versus');
  vs={diff,win:false,bot:BotGame(diff),pIn:[],bIn:[]};
}
function vsResolve(atk,inq){ // cancel queued garbage with attack, return leftover
  while(atk>0&&inq.length){
    if(inq[0]<=atk){atk-=inq[0];inq.shift();}
    else{inq[0]-=atk;atk=0;}
  }
  return atk;
}
function addGarbage(n){ // ponytail: hole column re-rolled per row
  for(let i=0;i<n;i++){
    if(board[0].some(c=>c))return gameOver();
    const hole=Math.random()*COLS|0;
    board.shift();
    const row=Array(COLS).fill('G');row[hole]=0;board.push(row);
  }
}
function meter(x,sum){
  if(sum<=0)return;
  const h=Math.min(sum,ROWS)*CELL;
  ctx.fillStyle='#ef4a4a';ctx.fillRect(x,BY+ROWS*CELL-h,6,h);
}
function drawBot(g){
  const bx=370;
  ctx.fillStyle='rgba(0,0,0,'+(BGV/100)+')';ctx.fillRect(bx,BY,COLS*CELL,ROWS*CELL);
  ctx.lineWidth=2;ctx.strokeStyle='#e8ebf5';ctx.strokeRect(bx-1,BY-1,COLS*CELL+2,ROWS*CELL+2);
  for(let y=HID;y<ROWS+HID;y++)for(let x=0;x<COLS;x++)
    if(g.board[y][x])block(bx+x*CELL,BY+(y-HID)*CELL,CELL,SHAPES[g.board[y][x]].c);
  if(g.cur)for(let y=0;y<g.cur.m.length;y++)for(let x=0;x<g.cur.m[y].length;x++)
    if(g.cur.m[y][x]&&g.cur.y+y>=HID)block(bx+(g.cur.x+x)*CELL,BY+(g.cur.y+y-HID)*CELL,CELL,SHAPES[g.cur.t].c);
}
function drawQuitBar(){
  // ponytail: 48px min so the text always sits on the bar, up to 18% of screen height
  const p=Math.min(1,quitHold/QUIT_HOLD);
  quitEl.style.display='flex';
  quitEl.style.height=(48+p*(innerHeight*0.18-48))+'px';
}
function hideQuitBar(){quitEl.style.display='none';}
function drawOver(){
  ctx.fillStyle='rgba(5,6,10,0.7)';ctx.fillRect(0,0,600,660);
  const isVs=mode=='versus'&&vs;
  const md=MODES[mode];
  const won=isVs?vs.win:(md&&((md.goal&&lines>=md.goal)||mode=='ultra'));
  const accent=won?'#ffd75e':'#ef4a4a';
  text(isVs?(vs.win?'VICTORY':'DEFEAT'):(won?'COMPLETE':'GAME OVER'),300,240,40,accent,'center');
  ctx.fillStyle=accent;ctx.fillRect(264,258,72,3);
  text(isVs?'VS AI - '+DIFFS[vs.diff-1].name:md.label,300,282,12,'#6b7288','center');
  if(isVs||mode=='sprint')text('TIME  '+fmtTime(time),300,330,22,'#e8ebf5','center');
  else text('SCORE  '+score,300,330,22,'#e8ebf5','center');
  text('LINES '+lines+'   PIECES '+pieces,300,360,12,'#9aa1b5','center');
  button(220,400,160,36,'r - retry',()=>isVs?startVs(vs.diff):startMode(mode));
  button(220,444,160,36,'esc - menu',()=>{goMenu();});
}

// --- input ---
addEventListener('keydown',e=>{
  needsDraw=true;
  if(Object.values(keybinds).includes(e.code))e.preventDefault();
  if(state=='menu'){
    const i=['Digit1','Digit2','Digit3','Digit4','Digit5','Numpad1','Numpad2','Numpad3','Numpad4','Numpad5'].indexOf(e.code)%5;
    const k=Object.keys(MODES);
    if(i>=0&&k[i]){k[i]=='versus'?(goPlay(),state='diff'):startMode(k[i]);}
    return;
  }
  if(state=='diff'){
    const i=['Digit1','Digit2','Digit3','Digit4','Digit5','Numpad1','Numpad2','Numpad3','Numpad4','Numpad5'].indexOf(e.code)%5;
    if(i>=0)startVs(i+1);
    if(e.code=='Escape'||e.code==keybinds.quit)goMenu();
    return;
  }
  if(state=='config'){
    if(e.code=='Escape'){if(rebindAction)rebindAction=null;else goMenu();}
    else if(rebindAction){
      keybinds[rebindAction]=e.code;
      lsSet('webtris_keys',keybinds);
      rebindAction=null;
    }
    return;
  }
  if(state=='over'){
    if(e.code==keybinds.retry)(mode=='versus'?startVs(vs.diff):startMode(mode));
    if(e.code=='Escape'||e.code==keybinds.quit)goMenu();
    return;
  }
  keys[e.code]=true;
  if(e.repeat)return;
  if(e.code==keybinds.left){moveDir=-1;dasT=0;arrT=0;tryMove(-1,0);}
  else if(e.code==keybinds.right){moveDir=1;dasT=0;arrT=0;tryMove(1,0);}
  else if(e.code==keybinds.rotCCW)rotate(-1);
  else if(e.code==keybinds.rotCW||e.code=='ArrowUp')rotate(1);
  else if(e.code==keybinds.hardDrop)hardDrop();
  else if(e.code==keybinds.hold||e.code=='ShiftLeft')doHold();
  else if(e.code==keybinds.retry)(mode=='versus'?startVs(vs.diff):startMode(mode));
});
addEventListener('keyup',e=>{
  keys[e.code]=false;
  if(e.code==keybinds.quit||e.code=='Escape')quitHold=0; // release cancels the quit fill, game never pauses
  if(e.code==keybinds.left&&moveDir==-1){
    if(keys[keybinds.right]){moveDir=1;dasT=0;arrT=0;tryMove(1,0);}else moveDir=0;
  }
  if(e.code==keybinds.right&&moveDir==1){
    if(keys[keybinds.left]){moveDir=-1;dasT=0;arrT=0;tryMove(-1,0);}else moveDir=0;
  }
});
cvs.addEventListener('click',e=>{
  const r=cvs.getBoundingClientRect();
  const mx=(e.clientX-r.left)*(cvs.width/r.width);
  const my=(e.clientY-r.top)*(cvs.height/r.height);
  for(const z of clickZones)
    if(mx>=z.x&&mx<z.x+z.w&&my>=z.y&&my<z.y+z.h){z.fn(mx,my);needsDraw=true;return;}
});
cvs.addEventListener('mousemove',e=>{
  const r=cvs.getBoundingClientRect();
  mouseX=(e.clientX-r.left)*(cvs.width/r.width);
  mouseY=(e.clientY-r.top)*(cvs.height/r.height);
  needsDraw=true;
});
cvs.addEventListener('mouseleave',()=>{mouseX=mouseY=-1;needsDraw=true;});

let last=performance.now();
function loop(now){
  const dt=Math.min(50,now-last);last=now;
  update(dt);
  const easing=state=='menu'?menuHover.some(v=>v>.001&&v<.999):state=='config'&&backHover>.001&&backHover<.999;
  if(state=='play'||state!=lastState||needsDraw||easing){draw();needsDraw=false;}
  lastState=state;
  requestAnimationFrame(loop);
}
goMenu(); // ponytail: menu fills window on first load so buttons sit at the real screen edge
addEventListener('resize',()=>{if(state=='menu')goMenu();needsDraw=true;}); // keep buttons flush to edge on window resize
requestAnimationFrame(loop);
