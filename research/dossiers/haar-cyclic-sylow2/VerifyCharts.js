const data = {"finiteH3":{"motif":"theta","L":8,"paths":[[[0,0,0,0],[1,0,0,1],[0,0,0,1],[1,1,1,1],[0,1,1,1],[1,0,2,1],[0,0,2,1],[1,1,0,1],[0,1,0,1]],[[0,0,0,0],[1,0,0,0],[0,0,0,2],[1,0,0,2],[0,1,2,2],[1,1,2,0],[0,0,1,0],[1,0,1,1],[0,1,0,1]],[[0,0,0,0],[1,1,1,0],[0,1,1,0],[1,0,2,0],[0,0,2,0],[1,1,0,0],[0,1,0,2],[1,1,0,2],[0,1,0,1]]]},"haarTheta":[[[0,0,0],[1,0,1],[0,0,1],[1,1,1],[0,1,1],[1,2,1],[0,2,1],[1,3,1],[0,3,1],[1,4,1],[0,4,1],[1,5,1],[0,5,0],[1,5,0],[0,4,0],[1,4,0],[0,4,-1]],[[0,0,0],[1,0,0],[0,0,-1],[1,1,-1],[0,1,-2],[1,2,-2],[0,2,-3],[1,3,-3],[0,3,-3],[1,4,-3],[0,4,-3],[1,5,-3],[0,5,-3],[1,5,-2],[0,5,-2],[1,5,-1],[0,4,-1]],[[0,0,0],[1,1,0],[0,1,0],[1,2,0],[0,2,0],[1,3,0],[0,3,-1],[1,3,-1],[0,2,-1],[1,2,-1],[0,2,-2],[1,3,-2],[0,3,-2],[1,4,-2],[0,4,-2],[1,4,-1],[0,4,-1]]],"haarBarbell":[[[0,0,0],[1,0,0],[0,-1,0],[1,-1,0],[0,-2,0],[1,-2,0],[0,-3,0],[1,-3,1],[0,-3,1],[1,-2,1],[0,-2,1],[1,-2,2],[0,-2,2],[1,-1,2],[0,-1,1],[1,0,1]],[[0,-3,0],[1,-3,0],[0,-4,0],[1,-4,0],[0,-5,0],[1,-5,0],[0,-6,0],[1,-6,0],[0,-7,0],[1,-7,0],[0,-8,0],[1,-8,0],[0,-8,-1],[1,-8,-1],[0,-8,-2],[1,-8,-2],[0,-9,-2]],[[0,-9,-2],[1,-9,-2],[0,-10,-2],[1,-10,-2],[0,-11,-2],[1,-11,-2],[0,-12,-2],[1,-12,-1],[0,-12,-1],[1,-11,-1],[0,-11,-1],[1,-11,0],[0,-11,0],[1,-10,0],[0,-10,-1],[1,-9,-1]]],"rails3Mixed":[[[0,0,0],[1,0,0],[1,0,1],[1,0,2],[0,0,2],[0,1,2],[1,1,2],[1,1,1],[0,1,1]],[[0,0,0],[0,1,0],[0,2,0],[0,3,0],[1,3,0],[1,3,1],[0,3,1],[0,2,1],[0,1,1]],[[0,0,0],[0,-1,0],[0,-2,0],[1,-2,0],[1,-2,1],[0,-2,1],[0,-1,1],[0,0,1],[0,1,1]]],"rails3Both":[[[0,0,0],[1,0,0],[1,0,1],[1,0,2],[1,0,3],[0,0,3],[0,1,3],[1,1,3],[1,1,2]],[[0,0,0],[0,1,0],[0,2,0],[1,2,0],[1,2,1],[1,2,2],[0,2,2],[0,1,2],[1,1,2]],[[0,0,0],[0,-1,0],[1,-1,0],[1,-1,1],[0,-1,1],[0,0,1],[0,1,1],[1,1,1],[1,1,2]]],"railsGeneral":[[[0,0,0],[1,0,0],[1,0,1],[1,0,2],[1,0,3],[0,0,3],[0,1,3],[1,1,3],[1,1,2]],[[0,0,0],[0,1,0],[0,2,0],[1,2,0],[1,2,1],[1,2,2],[0,2,2],[0,1,2],[1,1,2]],[[0,0,0],[0,-1,0],[1,-1,0],[1,-1,1],[0,-1,1],[0,0,1],[0,1,1],[1,1,1],[1,1,2]]]};

function mod(x,m) { return ((x%m)+m)%m; }
function key(v) { return v.join(","); }
function project(v,p,d,b) {
 const [side,x,y]=v;
 return [side,mod(x+b*y,d),mod(x,p),mod(y,p)];
}
function validEdge(a,b,p,d,bMark,kind) {
 const [layer,g,x,y]=a, [next,h,z,w]=b;
 const dx=mod(z-x,p),dy=mod(w-y,p),dg=mod(h-g,d);
 if (kind==="H"){
   if (layer===next) return false;
   const s=layer===0?1:-1;
   return (dx===0&&dy===0&&dg===0) ||
      (dx===mod(s,p)&&dy===0&&dg===mod(s,d)) ||
      (dx===0&&dy===mod(s,p)&&dg===mod(s*bMark,d));
 }
 if (layer!==next) return dx===0&&dy===0&&dg===0;
 if (layer===0) return dy===0&&[1,-1].some(s=>dx===mod(s,p)&&dg===mod(s,d));
 return dx===0&&[1,-1].some(s=>dy===mod(s,p)&&dg===mod(s*bMark,d));
}
function validIntegerEdge(a,b,kind) {
 const [layer,x,y]=a,[next,z,w]=b;
 const dx=z-x,dy=w-y;
 if (kind==="H"){
   if(layer===next)return false;
   const s=layer===0?1:-1;
   return (dx===0&&dy===0)||(dx===s&&dy===0)||(dx===0&&dy===s);
 }
 if(layer!==next)return dx===0&&dy===0;
 return layer===0?Math.abs(dx)===1&&dy===0:dx===0&&Math.abs(dy)===1;
}
function layout(motif,L,paths,adjacent) {
 function ensure(ok){if(!ok)throw Error("Invalid "+motif+" certificate");}
 const [a,b,c]=paths;
 const set=rows=>new Set(rows.map(key));
 function path(rows,n,cycle=false){
  ensure(rows.length===n && set(rows).size===n);
  for(let t=1;t<n;t++)ensure(adjacent(rows[t-1],rows[t]));
  if(cycle)ensure(adjacent(rows.at(-1),rows[0]));
 }
 if(motif==="theta"){
  for(const row of paths){
   path(row,L+1);
   ensure(key(row[0])===key(a[0])&&key(row.at(-1))===key(a.at(-1)));
  }
  ensure(set(paths.flat()).size===3*L-1);
 } else {
  path(a,L,true);path(c,L,true);path(b,L+1);
  ensure(set(a).has(key(b[0]))&&set(c).has(key(b.at(-1))));
  ensure(set(paths.flat()).size===3*L-1);
 }
}
function auditInteger(motif,L,paths,p,d,b,kind) {
 layout(motif,L,paths,(x,y)=>validIntegerEdge(x,y,kind));
 const mapped=paths.map(row=>row.map(v=>project(v,p,d,b)));
 layout(motif,L,mapped,(x,y)=>validEdge(x,y,p,d,b,kind));
}
layout("theta",8,data.finiteH3.paths,(x,y)=>validEdge(x,y,3,2,0,"H"));
auditInteger("theta",16,data.haarTheta,5,2,0,"H");
auditInteger("theta",16,data.haarTheta,3,4,2,"H");
auditInteger("barbell",16,data.haarBarbell,3,4,0,"H");
auditInteger("theta",8,data.rails3Mixed,3,2,0,"K");
auditInteger("theta",8,data.rails3Both,3,2,1,"K");
auditInteger("theta",8,data.railsGeneral,5,2,0,"K");
const scale = paths => {
 const all=paths.flat();
 return [1,2].map(k=>Math.max(...all.map(p=>p[k]))-Math.min(...all.map(p=>p[k])));
};
if(scale(data.haarTheta).some(i=>i>=7)||scale(data.railsGeneral).some(i=>i>=5))
 throw Error("Large-prime injectivity bounds");
let tested=0;
for (const p of [3,5,7,11,13,17,19,23,29,31]) {
 for(let d=2;d<=128;d*=2)for(let b=0;b<d;b++){
  if(b%2===0){
   if(p===3&&d===2)layout("theta",8,data.finiteH3.paths,(x,y)=>validEdge(x,y,p,d,b,"H"));
   else if(p===3&&b%4===0)auditInteger("barbell",16,data.haarBarbell,p,d,b,"H");
   else auditInteger("theta",16,data.haarTheta,p,d,b,"H");
   tested++;
  }
  const rail=p===3?(b%2===0?data.rails3Mixed:data.rails3Both):data.railsGeneral;
  auditInteger("theta",8,rail,p,d,b,"K");
  tested++;
 }
}
console.log(JSON.stringify({baseProfiles:7, tested,haarSpans:scale(data.haarTheta),railSpans:scale(data.railsGeneral)}));
