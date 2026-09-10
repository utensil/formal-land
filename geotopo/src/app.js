"use strict";
const DATA = JSON.parse(document.getElementById("route-data").textContent);
const RM = DATA.roadmap, PRS = DATA.prs, NODES = RM.nodes, GOALS = RM.routes;
// These are the SpinRep route, node-state, activity and health palettes.
const PALETTE = ["#6d9cbe", "#6b8e23", "#cc7833", "#7570b3", "#a5c261", "#bc9458", "#da4939"];
const ST = {done:"landed / available", review:"in review", open:"future milestone", branch:"next handoff", incomplete:"partial / unfinished"};
const TL_STATE = {D:"#8fa3b8", R:"#6d9cbe", V:"#e5c07b", T:"#a5c261", M:"#7fb069", C:"#c97b7b"};
const TL_NAME = {D:"draft", R:"open / revision", V:"review", T:"ready to merge", M:"merged", C:"closed, unmerged"};
const byId = new Map(NODES.map(n => [n.id, n]));
const byPR = new Map(PRS.map(p => [p.number, p]));
const byEdge = new Map(RM.edges.map(e => [e.id, e]));
const routeNodes = new Map(GOALS.map(g => [g.id, new Set(g.edges.flatMap(id => {const e=byEdge.get(id);return [e.fromNode,e.toNode];}))]));
const state = {routes:new Set(GOALS.map(g=>g.id)), cohort:"all", node:null};
const $ = id => document.getElementById(id);
const esc = x => String(x ?? "").replace(/[&<>"']/g, c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const url = value => /^https:\/\/(github\.com|utensil\.github\.io)\//.test(value || "") ? value : "#";
const sourceLink = (value,label="source") => `<a href="${esc(url(value))}" target="_blank" rel="noopener">${esc(label)}</a>`;
const dateTime = t => new Intl.DateTimeFormat("en-GB",{timeZone:RM.timezone,day:"2-digit",month:"short",hour:"2-digit",minute:"2-digit",hour12:false}).format(new Date(t))+" SGT";
const ms = value => new Date(value).getTime();
const shortTitle = p => p.title.replace(/^(?:feat|refactor|docs|chore)(?:\([^)]*\))?:\s*/, "");
function prLink(p) {return `<a class="prlink pr-${p.state === "merged" ? "merged" : p.state === "closed" ? "closed" : p.state === "draft" ? "draft" : "open"}${!p.worked && p.state === "merged" ? " pr-upstream" : ""}" href="${esc(url(p.url))}" target="_blank" rel="noopener">#${p.number}</a>`;}
const nodePrs = id => PRS.filter(p=>p.nodes.includes(id));
const goalPrs = g => PRS.filter(p=>p.nodes.some(id=>routeNodes.get(g.id).has(id)));
function nodeState(n) {
  const ps=nodePrs(n.id);
  if (!ps.length) return n.status;
  if (ps.some(p=>p.state === "open" || p.state === "draft")) return "review";
  if (ps.some(p=>p.state === "merged")) return "done";
  return "incomplete";
}
function visiblePrs() {return PRS.filter(p=>(state.cohort !== "worked" || p.worked) && (state.cohort !== "reviewed" || p.reviewed) && GOALS.some(g=>state.routes.has(g.id) && p.nodes.some(n=>routeNodes.get(g.id).has(n))));}
const band = value => value >= 75 ? "#7fb069" : value >= 60 ? "#e5c07b" : "#c97b7b";

function renderLegend() {
  $("legend").innerHTML = `<div class="legrow"><span>routes:</span>${GOALS.map(g=>`<button class="gl" data-g="${g.id}" aria-pressed="true" title="Toggle route ${esc(g.symbol)} and its chart cohort"><span class="sw" style="background:${PALETTE[g.color]}"></span>${esc(g.symbol)}</button>`).join("")}<span style="margin:0 10px">|</span><span class="st"><span style="width:13px;height:13px;border-radius:50%;border:1.2px solid #e6e1dc;margin-right:5px"></span>junction · routes meet</span><span style="margin:0 10px">|</span><span class="st"><span style="width:16px;height:16px;border-radius:50%;border:2.8px solid #e6e1dc;margin-right:5px"></span>summit</span></div><div class="legrow"><span>node state:</span>${Object.entries(ST).map(([key,label])=>`<span class="st"><span class="dot nodest-${key}"></span>${esc(label)}</span>`).join("")}<span style="margin:0 10px">|</span><span>PR activity:</span>${Object.entries(TL_NAME).map(([key,label])=>`<span class="st"><span class="dot" style="background:${TL_STATE[key]}"></span>${esc(label)}</span>`).join("")}</div>`;
  $("legend").querySelectorAll("[data-g]").forEach(el=>{
    el.addEventListener("click",()=>{state.routes.has(el.dataset.g) ? state.routes.delete(el.dataset.g) : state.routes.add(el.dataset.g);el.classList.toggle("off",!state.routes.has(el.dataset.g));el.setAttribute("aria-pressed",String(state.routes.has(el.dataset.g)));hideTip();refreshRoutes();renderCharts();});
    bindRouteHover(el,el.dataset.g);
  });
}
function renderGoals() {
  $("goals").innerHTML = GOALS.map(g=>{
    const ps=goalPrs(g), merged=ps.filter(p=>p.state==="merged").length, open=ps.filter(p=>p.state==="open"||p.state==="draft").length;
    return `<div class="goal" data-g="${g.id}" style="--gc:${PALETTE[g.color]}"><h3><span class="sw" style="background:${PALETTE[g.color]}"></span>Route ${esc(g.symbol)} — ${esc(g.title)}</h3><div class="bar"><i style="width:${ps.length ? merged/ps.length*100 : 0}%;background:${PALETTE[g.color]}"></i></div><div class="pct">${merged} / ${ps.length} tracked PRs landed · ${open} open · ${ps.length-merged-open} closed<br>PR delivery, not completion of the summit.</div><div class="route-lbl">route branches</div>${g.displayPaths.map(path=>`<div class="route">${path.map(id=>`<button data-node-link="${id}">${esc(byId.get(id).label)}</button>`).join('<span class="sep">→</span>')}</div>`).join("")}<div class="work">${ps.map(prLink).join(" · ")}</div><div class="eval">${esc(g.insight)}</div><div class="rdev"><b>Next handoff:</b> ${g.frontier.map(id=>`${esc(byId.get(id).label)} <span class="status-${nodeState(byId.get(id))}">(${esc(ST[nodeState(byId.get(id))])})</span>`).join(" · ")}</div></div>`;
  }).join("");
  $("goals").querySelectorAll(".goal").forEach(el=>bindRouteHover(el,el.dataset.g));
  $("goals").querySelectorAll("[data-node-link]").forEach(el=>el.addEventListener("click",()=>selectNode(el.dataset.nodeLink,true)));
}

const W=1560, ROW=94, TOP=70, X0=370, X1=1450;
const H=TOP+(RM.rows.length-1)*ROW+85;
const positions=new Map();
RM.rows.forEach((row,r)=>{
  const nodes=NODES.filter(n=>n.row===row.id);
  nodes.forEach((n,i)=>positions.set(n.id,{x:n.x ?? (nodes.length===1 ? (X0+X1)/2 : X0+i*(X1-X0)/(nodes.length-1)),y:TOP+r*ROW}));
});
function edgePath(a,b,off=0) {
  const dx=b.x-a.x,dy=b.y-a.y,len=Math.hypot(dx,dy)||1,nx=-dy/len,ny=dx/len;
  const p={x:a.x+nx*off,y:a.y+ny*off},q={x:b.x+nx*off,y:b.y+ny*off};
  const mx=(p.x+q.x)/2,my=(p.y+q.y)/2,bend=Math.min(24,len*.12);
  // A long vertical edge bows around intermediate nodes instead of passing through them.
  if(Math.abs(dx)<20 && Math.abs(dy)>ROW*1.4)return `M${p.x},${p.y} C${p.x+85},${p.y+dy*.33} ${q.x+85},${p.y+dy*.67} ${q.x},${q.y}`;
  if (Math.abs(dy)<1) return `M${p.x},${p.y} C${p.x+dx*.3},${p.y+28+off} ${p.x+dx*.7},${q.y+28+off} ${q.x},${q.y}`;
  return `M${p.x},${p.y} C${mx-dy/len*bend},${my+dx/len*bend} ${mx+dy/len*bend},${my-dx/len*bend} ${q.x},${q.y}`;
}
function labelLines(label,max=24) {
  if(label.length<=max)return [label];
  const words=label.split(" "),lines=[""];
  words.forEach(word=>{if(lines[lines.length-1].length+word.length>max)lines.push(word);else lines[lines.length-1]+=(lines[lines.length-1]?" ":"")+word;});
  return lines;
}
function renderMap() {
  let html=`<title id="map-title">Geometric topology: contribution routes in the overall roadmap</title><desc id="map-desc">${NODES.length} milestone nodes across all eleven layers. Gray dependencies and three colored routes; select nodes for evidence.</desc>`;
  RM.rows.forEach((row,i)=>html+=`<text class="lrow" x="305" y="${TOP+i*ROW+6}" text-anchor="end" style="font-size:21px">${esc(row.label)}</text>`);
  RM.edges.forEach(e=>html+=`<path class="edge edge-dep" d="${edgePath(positions.get(e.fromNode),positions.get(e.toNode))}"><title>${esc(byId.get(e.fromNode).label)} → ${esc(byId.get(e.toNode).label)}</title></path>`);
  GOALS.forEach(g=>g.edges.forEach(id=>{
    const edge=byEdge.get(id),shared=GOALS.filter(other=>other.edges.includes(id)),off=(shared.indexOf(g)-(shared.length-1)/2)*5.5;
    html+=`<path class="edge edge-goal" data-goal="${g.id}" stroke="${PALETTE[g.color]}" d="${edgePath(positions.get(edge.fromNode),positions.get(edge.toNode),off)}"/>`;
  }));
  NODES.forEach(n=>{
    const p=positions.get(n.id),goals=GOALS.filter(g=>routeNodes.get(g.id).has(n.id)),summits=GOALS.filter(g=>g.summit===n.id),ps=nodePrs(n.id),lines=labelLines(n.label);
    html+=`<g class="node" data-id="${n.id}" data-goals="${goals.map(g=>g.id).join(" ")}" tabindex="0" role="button" aria-label="${esc(n.label)}; ${esc(ST[nodeState(n)])}; ${ps.length} tracked PRs">${summits.map(g=>`<circle class="summit-halo" r="25" cx="${p.x}" cy="${p.y}" fill="${PALETTE[g.color]}"/><circle r="18" cx="${p.x}" cy="${p.y}" fill="none" style="stroke:${PALETTE[g.color]};stroke-width:2.8"/>`).join("")}<circle class="main nodest-${nodeState(n)}" cx="${p.x}" cy="${p.y}" r="13"/>${goals.length>1?`<circle class="junction" r="4" cx="${p.x}" cy="${p.y}"/>`:""}${lines.map((line,i)=>`<text class="nl" x="${p.x}" y="${p.y-20-(lines.length-1-i)*18}" text-anchor="middle">${esc(line)}</text>`).join("")}${ps.length?`<text class="ownmark" x="${p.x}" y="${p.y+33}" text-anchor="middle">${ps.map(p=>`#${p.number}${p.reviewed?" ◌":""}`).join(" · ")}</text>`:""}</g>`;
  });
  $("map").setAttribute("viewBox",`0 0 ${W} ${H}`);$("map").innerHTML=html;
  $("map").querySelectorAll(".edge-goal").forEach(el=>bindRouteHover(el,el.dataset.goal));
  $("map").querySelectorAll(".node").forEach(el=>{
    el.addEventListener("mouseenter",()=>{lightRoutes((el.dataset.goals||"").split(" "));showTip(nodeContent(byId.get(el.dataset.id)),el);});
    el.addEventListener("mouseleave",()=>{lightRoutes([]);scheduleHide();});
    el.addEventListener("click",()=>{selectNode(el.dataset.id);showTip(nodeContent(byId.get(el.dataset.id)),el,true);});
    el.addEventListener("keydown",e=>{if(e.key==="Enter"||e.key===" "){e.preventDefault();selectNode(el.dataset.id);showTip(nodeContent(byId.get(el.dataset.id)),el,true);}});
  });
}
function nodeContent(n) {
  const ps=nodePrs(n.id),dependent=RM.edges.filter(e=>e.fromNode===n.id).map(e=>byId.get(e.toNode).label);
  return `<b>${esc(n.label)}</b><div class="tstatus">${esc(n.layer)} · ${esc(ST[nodeState(n)])}</div><p>${esc(n.summary)}</p>${ps.length?`<div class="tstatus">Our work: ${ps.map(p=>`${prLink(p)} · ${esc(p.state)}${p.reviewed?" · reviewed by us":""}`).join("<br>")}</div>`:`<div class="tstatus">Roadmap context · no selected PR</div>`}${n.remaining?`<p><strong>Handoff:</strong> ${esc(n.remaining)}</p>`:""}${dependent.length?`<div class="tstatus">Feeds: ${esc(dependent.join(" · "))}</div>`:""}<div class="tstatus">${sourceLink(n.source,"pinned roadmap")}</div>`;
}
function selectNode(id,scroll=false) {
  const n=byId.get(id);if(!n)return;
  state.node=id;$("map-detail").innerHTML=nodeContent(n);
  $("map").querySelectorAll(".node").forEach(el=>el.classList.toggle("selected",el.dataset.id===id));
  if(scroll){
    const target=$("map").querySelector(`.node[data-id="${id}"]`);
    const viewport=$("map").parentElement,box=target.getBoundingClientRect(),frame=viewport.getBoundingClientRect();
    viewport.scrollLeft+=box.left+box.width/2-frame.left-viewport.clientWidth/2;
    window.scrollBy({top:box.top+box.height/2-innerHeight/2,behavior:"instant"});
    target.focus({preventScroll:true});
  }
}
function lightRoutes(ids) {
  const active=new Set(ids.filter(id=>state.routes.has(id)));
  document.querySelectorAll(".edge-goal").forEach(el=>el.classList.toggle("lit",active.has(el.dataset.goal)));
  document.querySelectorAll(".goal").forEach(el=>el.classList.toggle("lit",active.has(el.dataset.g)));
}
function bindRouteHover(el,id) {el.addEventListener("mouseenter",()=>lightRoutes([id]));el.addEventListener("mouseleave",()=>lightRoutes([]));el.addEventListener("focus",()=>lightRoutes([id]));el.addEventListener("blur",()=>lightRoutes([]));}
function refreshRoutes() {
  document.querySelectorAll(".edge-goal").forEach(el=>el.style.display=state.routes.has(el.dataset.goal)?"":"none");
  document.querySelectorAll(".goal").forEach(el=>el.classList.toggle("off",!state.routes.has(el.dataset.g)));
  document.querySelectorAll(".node").forEach(el=>{const ids=el.dataset.goals.split(" ").filter(Boolean);el.classList.toggle("dim",ids.length>0&&!ids.some(id=>state.routes.has(id)));});
}

let hideTimer=null,pinned=false;
function hideTip(){pinned=false;$("tip").style.display="none";}
function scheduleHide(){clearTimeout(hideTimer);hideTimer=setTimeout(()=>{if(!pinned&&!$("tip").matches(":hover"))hideTip();},350);}
function showTip(html,target,pin=false) {
  if(pinned&&!pin)return;
  clearTimeout(hideTimer);pinned=pin;
  const tip=$("tip");tip.innerHTML=`<button class="close-tip" aria-label="Close details">×</button>${html}`;tip.style.display="block";
  tip.querySelector(".close-tip").addEventListener("click",hideTip);
  const r=target.getBoundingClientRect(),box=tip.getBoundingClientRect();
  tip.style.left=Math.max(10,Math.min(r.left+r.width/2-box.width/2,innerWidth-box.width-10))+"px";
  tip.style.top=Math.max(10,Math.min(r.bottom+8,innerHeight-box.height-10))+"px";
  tip.querySelectorAll("[data-jump-pr]").forEach(button=>button.addEventListener("click",()=>{const p=byPR.get(Number(button.dataset.jumpPr));hideTip();selectNode(p.nodes[0],true);}));
}
$("tip").addEventListener("mouseenter",()=>clearTimeout(hideTimer));$("tip").addEventListener("mouseleave",scheduleHide);
document.addEventListener("keydown",e=>{if(e.key==="Escape")hideTip();});

function transitions(pr) {
  const firstDraftChange=pr.events.filter(e=>e.kind==="ready_for_review"||e.kind==="convert_to_draft").sort((a,b)=>ms(a.at)-ms(b.at))[0];
  const all=[{at:pr.created_at,state:firstDraftChange?.kind==="ready_for_review"?"D":"R",label:"opened"}];
  for(const e of pr.events) {
    let next=null;
    if(e.kind==="labeled") next=({"awaiting-CI":"R","awaiting-author":"R","awaiting-review":"V","review-in-progress":"V","ready-to-merge":"T"})[e.label];
    if(e.kind==="convert_to_draft")next="D";
    if(e.kind==="ready_for_review"||e.kind==="reopened")next="R";
    if(e.kind==="closed"&&!pr.merged_at)next="C";
    if(next)all.push({at:e.at,state:next,label:e.label||e.kind});
  }
  if(pr.merged_at)all.push({at:pr.merged_at,state:"M",label:"merged"});
  else if(pr.closed_at)all.push({at:pr.closed_at,state:"C",label:"closed"});
  const result=[];let last=null;
  all.sort((a,b)=>ms(a.at)-ms(b.at)).forEach(e=>{if(e.state!==last){result.push({...e,number:pr.number});last=e.state;}});
  return result;
}
const EVENTS=PRS.flatMap(transitions);
const SIX=6*3600e3,DAY=24*3600e3,SGT=8*3600e3;
const floorSlot=t=>Math.floor((t+SGT)/SIX)*SIX-SGT;
const t0=floorSlot(Math.min(...PRS.map(p=>ms(p.created_at)))),t1=floorSlot(ms(DATA.collected_at))+SIX;
const slots=Array.from({length:Math.round((t1-t0)/SIX)},(_,i)=>t0+i*SIX);
const CW=Math.max(1560,slots.length*20+90),LEFT=60,RIGHT=CW-30,STEP=(RIGHT-LEFT)/slots.length;
const xOf=t=>LEFT+(t-t0)/(t1-t0)*(RIGHT-LEFT);
const dayKey=t=>new Date(t+SGT).toISOString().slice(0,10);
const median=a=>{const s=a.slice().sort((x,y)=>x-y);return s.length%2?s[(s.length-1)/2]:(s[s.length/2-1]+s[s.length/2])/2;};
function axis(baseline) {
  let result="",prev="";
  slots.forEach((t,i)=>{const day=dayKey(t);if(day!==prev){result+=`<text x="${LEFT+(i+.5)*STEP}" y="${baseline+17}" font-size="11" fill="#8a857e" text-anchor="middle">${day.slice(5)}</text>`;prev=day;}});
  return result;
}
function chartBind(host,selector,content) {
  host.querySelectorAll(selector).forEach(el=>{
    el.addEventListener("mouseenter",()=>showTip(content(el),el));el.addEventListener("mouseleave",scheduleHide);
    el.addEventListener("click",()=>showTip(content(el),el,true));
    el.addEventListener("keydown",e=>{if(e.key==="Enter"||e.key===" "){e.preventDefault();showTip(content(el),el,true);}});
  });
}
function renderActivity(visible) {
  const ids=new Set(visible.map(p=>p.number)),events=EVENTS.filter(e=>ids.has(e.number));
  const groups=new Map(slots.map(t=>[t,[]]));events.forEach(e=>groups.get(floorSlot(ms(e.at)))?.push(e));
  const max=Math.max(1,...[...groups.values()].map(e=>e.length)),PER=9,plot=Math.max(126,max*PER),baseline=35+plot;
  let html=`<svg viewBox="0 0 ${CW} ${baseline+35}" role="img" aria-label="State transitions per six-hour window"><line x1="40" y1="${baseline}" x2="${RIGHT+10}" y2="${baseline}" stroke="#444" stroke-dasharray="2 4"/>`;
  slots.forEach((t,i)=>{
    const es=groups.get(t);if(!es.length)return;
    const x=LEFT+i*STEP+3,bw=Math.max(3,STEP-6);let y=baseline;
    for(const st of ["D","R","V","T","M","C"]){const n=es.filter(e=>e.state===st).length;if(n){y-=n*PER;html+=`<rect x="${x}" y="${y}" width="${bw}" height="${n*PER}" fill="${TL_STATE[st]}" opacity=".85"/>`;}}
    html+=`<text x="${x+bw/2}" y="${y-6}" font-size="12" fill="#e6e1dc" text-anchor="middle" font-weight="700">${es.length}</text><g class="tlcol" data-slot="${t}" tabindex="0" role="button" aria-label="${esc(dateTime(t))}: ${es.length} transitions"><rect x="${x-3}" y="${y-20}" width="${bw+6}" height="${baseline-y+34}" fill="transparent"/></g>`;
  });
  html+=axis(baseline)+"</svg>";$("prtl").innerHTML=html;
  chartBind($("prtl"),".tlcol",el=>{const t=Number(el.dataset.slot),es=groups.get(t);return `<b>${esc(dateTime(t))} · 6-hour window</b><div class="tstatus">${es.length} state transitions</div>${es.map(e=>{const p=byPR.get(e.number);return `<div class="tstatus">${esc(dateTime(e.at))} · ${prLink(p)} → <span style="color:${TL_STATE[e.state]}">${TL_NAME[e.state]}</span><br>${esc(shortTitle(p))} · ${esc(e.label)}</div>`;}).join("")}`;});
  $("activity-note").textContent=`${visible.length} selected PRs · ${events.length} stage transitions · height = transitions in a 6-hour SGT window. Empty windows retain their time width. Consecutive duplicate stages are collapsed; commits and individual rubric verdicts are not stage transitions.`;
}
function healthContent(p) {
  const h=p.health,t=p.merged_at||p.closed_at||DATA.collected_at,verb=p.merged_at?"Merged":p.closed_at?"Closed, unmerged":"Open at snapshot";
  return `<b>${prLink(p)} · ${esc(shortTitle(p))}</b><div class="tstatus">${verb} · ${esc(dateTime(t))}</div><div class="tstatus">${p.worked?"Worked on":"Reviewed-only"}${p.reviewed?" · reviewed by us":""}</div><div class="tstatus">${h.score==null?`Health unscored: ${esc(h.reason)}`:`Health <strong style="color:${band(h.score)}">${h.score}</strong> · ${Object.entries(h.terms).map(([k,v])=>`${k}=${v??"?"}`).join(" · ")}`}</div><div class="tstatus">Observed non-green rubrics: ${esc(h.failed.join(", ")||"none")}</div><div class="tstatus">Snapshot head: <code style="overflow-wrap:anywhere">${esc(p.head)}</code></div><div class="tstatus">${h.source?sourceLink(h.source,"exact-head scoreboard"):"No complete exact-head scoreboard"}${p.reviewEvidence.length?" · "+p.reviewEvidence.map(e=>sourceLink(e,"review evidence")).join(" · "):""}</div><div class="tstatus"><button data-jump-pr="${p.number}">Show contribution on the map</button></div>`;
}
function renderHealth(visible) {
  const top=55,plot=130,baseline=top+plot,yOf=h=>baseline-h/100*plot;
  let html=`<svg viewBox="0 0 ${CW} ${baseline+38}" role="img" aria-label="Public-review churn score at merge, close or snapshot time">`;
  [0,25,50,75,100].forEach(h=>{const y=yOf(h);html+=`<line x1="40" y1="${y}" x2="${RIGHT+10}" y2="${y}" stroke="#333" stroke-width=".6"/><text x="32" y="${y+4}" font-size="11" fill="#8a857e" text-anchor="end">${h}</text>`;});
  const merged=visible.filter(p=>p.merged_at&&p.health.score!=null),days=[...new Set(merged.map(p=>dayKey(ms(p.merged_at))))].sort();
  const med=days.map(day=>{const start=ms(day+"T00:00:00+08:00"),sample=merged.filter(p=>ms(p.merged_at)>=start-DAY&&ms(p.merged_at)<start+2*DAY);return {day,t:start+DAY/2,h:median(sample.map(p=>p.health.score)),count:sample.length};});
  if(med.length>1)html+=`<path d="${med.map((p,i)=>`${i?"L":"M"}${xOf(p.t)},${yOf(p.h)}`).join(" ")}" fill="none" stroke="#cc7833" stroke-width="1.5" opacity=".85"/>`;
  med.forEach((p,i)=>html+=`<g class="median-mark" data-median="${i}" tabindex="0" role="button" aria-label="${p.day} rolling median ${p.h}"><circle cx="${xOf(p.t)}" cy="${yOf(p.h)}" r="2.5" fill="#cc7833"/><circle cx="${xOf(p.t)}" cy="${yOf(p.h)}" r="9" fill="transparent"/></g>`);
  let unscored=0;
  visible.forEach(p=>{
    const x=xOf(ms(p.merged_at||p.closed_at||DATA.collected_at)),value=p.health.score,y=value==null?17+(unscored++%2)*17:yOf(value),r=5,color=value==null?"#e5c07b":band(value);
    let shape=p.state==="merged"?(p.worked?`<circle cx="${x}" cy="${y}" r="${r}" fill="${color}"/>`:`<rect x="${x-r}" y="${y-r}" width="${2*r}" height="${2*r}" fill="${color}"/>`):p.state==="closed"?`<path d="M${x} ${y-r} L${x+r} ${y} L${x} ${y+r} L${x-r} ${y} Z" fill="${color}"/>`:`<path d="M${x} ${y-r} L${x+r} ${y+r} L${x-r} ${y+r} Z" fill="${color}"/>`;
    if(p.reviewed)shape+=`<circle cx="${x}" cy="${y}" r="8.5" fill="none" stroke="#e6e1dc" stroke-width="1" stroke-dasharray="2 2"/>`;
    html+=`<g class="hp" data-pr="${p.number}" tabindex="0" role="button" aria-label="PR ${p.number}, ${esc(p.state)}, health ${value??"unscored"}">${shape}<circle cx="${x}" cy="${y}" r="12" fill="transparent"/><text x="${x-10}" y="${y-8}" text-anchor="end" fill="#9d9485" font-size="10">#${p.number}</text></g>`;
  });
  if(unscored)html+=`<text x="32" y="24" font-size="10" fill="#9d9485" text-anchor="end">n/a</text>`;
  html+=axis(baseline)+"</svg>";$("prhealth").innerHTML=html;
  chartBind($("prhealth"),".hp",el=>healthContent(byPR.get(Number(el.dataset.pr))));
  chartBind($("prhealth"),".median-mark",el=>{const p=med[Number(el.dataset.median)];return `<b>${p.day} · rolling median ${p.h}</b><div class="tstatus">${p.count} selected merged PRs in this SGT day and its two adjacent days. Unscored PRs are excluded. This is our cohort, with no background sample of unrelated PRs.</div>`;});
}
function renderCharts() {
  const visible=visiblePrs();renderActivity(visible);renderHealth(visible);
  $("work-summary").textContent=`Work behind the routes · ${visible.length} PRs in the current lens`;
  $("work-table").innerHTML=`<table><thead><tr><th>PR</th><th>Milestone</th><th>State</th><th>Our role</th><th>Health</th></tr></thead><tbody>${visible.map(p=>`<tr><td>${prLink(p)} · ${esc(shortTitle(p))}</td><td>${p.nodes.map(id=>esc(byId.get(id).label)).join(" · ")}</td><td>${esc(p.state)}</td><td>${p.worked?"worked on":""}${p.reviewed?" · reviewed":""}</td><td>${p.health.score??"unscored"}</td></tr>`).join("")}</tbody></table>`;
}
renderLegend();renderGoals();renderMap();renderCharts();
$("cohort").addEventListener("change",e=>{state.cohort=e.target.value;hideTip();renderCharts();});
let syncing=false;
[$("prtl"),$("prhealth")].forEach((el,i,all)=>el.addEventListener("scroll",()=>{if(syncing)return;syncing=true;all[1-i].scrollLeft=el.scrollLeft;requestAnimationFrame(()=>syncing=false);}));
const mergedCount=PRS.filter(p=>p.state==="merged").length,closedCount=PRS.filter(p=>p.state==="closed").length;
$("stats").textContent=`${NODES.length} milestones · ${RM.edges.length} cited dependencies · ${PRS.length} worked-on or reviewed PRs: ${mergedCount} merged, ${PRS.length-mergedCount-closedCount} open, ${closedCount} closed · ${PRS.filter(p=>p.reviewed).length} with verified review coverage. ◌ marks reviewed contributions. Toggle route chips to focus the charts.`;
$("sources").innerHTML=`<p>${sourceLink(RM.roadmapUrl,"Pinned GeometricTopology roadmap")} · ${sourceLink(RM.reference,"SpinRep design reference")}</p><p>Roadmap context checked ${esc(dateTime(RM.contextAsOf))}; PR snapshot refreshed ${esc(dateTime(DATA.collected_at))}. Only the explicit worked/reviewed selection is embedded. The review marker records verified coverage of the PR, not authorship of every public rubric observation.</p><p>Terminal PR evidence stays frozen during ordinary refreshes. Earlier overwritten review rounds cannot be reconstructed. Context nodes summarize milestones without importing the rest of the roadmap’s PR history.</p>`;
$("snapshot").innerHTML=`Snapshot ${esc(dateTime(DATA.collected_at))} · ${sourceLink("https://github.com/utensil/formal-land/tree/main/geotopo","data and update instructions")} · standalone HTML; no network requests.`;
