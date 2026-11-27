"use strict";
const C={"P":{"D":[[0,[0,0,0,0,0]],[4,[0,0,0,1,0]],[4,[0,1,0,1,0]],[0,[0,1,0,0,0]]],"B":[[1,2],[3,5],[4,7],[6,0]],"O":["0312"]},"Q":{"D":[[4,[0,0,0,0,0]],[4,[0,-1,0,0,0]],[1,[0,-1,0,-1,0]],[0,[1,-1,0,-1,0]],[0,[1,0,0,-1,0]],[1,[0,0,0,-1,0]]],"B":[[1,3],[2,4],[5,7],[6,8],[9,11],[10,0]],"O":["402315","023154","305412","054123"]},"R":{"D":[[4,[0,0,0,0,0]],[4,[0,-1,0,0,0]],[1,[0,-1,0,0,-1]],[4,[0,-1,0,1,-1]],[4,[0,0,0,1,-1]],[1,[0,0,0,0,-1]]],"B":[[1,3],[2,5],[4,6],[7,9],[8,10],[11,0]],"O":["054123","032451","024153"]},"S":{"D":[[3,[0,0,0,0,0]],[1,[0,0,0,0,-1]],[3,[0,0,0,1,-1]],[3,[0,0,-1,1,-1]],[1,[0,0,-1,0,-1]],[3,[0,0,-1,0,0]]],"B":[[1,3],[2,5],[4,6],[7,8],[9,11],[10,0]],"O":["043512"]},"T":{"D":[[4,[0,0,0,0,0]],[4,[0,-1,0,0,0]],[2,[0,-1,0,0,-1]],[3,[0,-1,1,0,-1]],[0,[0,-1,1,-1,-1]],[0,[0,0,1,-1,-1]],[3,[0,0,1,0,-1]],[2,[0,0,0,0,-1]]],"B":[[1,3],[2,4],[5,6],[7,9],[8,10],[11,13],[12,15],[14,0]],"O":["20734651","20473561","73046521"]},"U":{"D":[[4,[0,0,0,0,0]],[0,[1,-1,0,0,0]],[3,[1,-1,0,1,0]],[3,[1,-1,-1,1,0]],[0,[1,-1,-1,0,0]],[4,[0,0,-1,0,0]],[2,[0,0,-1,0,-1]],[2,[0,0,0,0,-1]]],"B":[[1,2],[3,5],[4,6],[7,9],[8,11],[10,12],[13,15],[14,0]],"O":["17034625","03462517"]},"V":{"D":[[4,[0,0,0,0,0]],[4,[0,-1,0,0,0]],[1,[0,-1,0,0,-1]],[1,[-1,-1,0,0,-1]],[4,[-1,-1,0,1,-1]],[4,[-1,0,0,1,-1]],[1,[-1,0,0,0,-1]],[1,[0,0,0,0,-1]]],"B":[[1,3],[2,5],[4,7],[6,8],[9,11],[10,12],[13,14],[15,0]],"O":["03526174"]}};
const ok=(x,m)=>{if(!x)throw Error(m)};
const same=(x,y)=>x.join()===y.join(),plus=(x,y)=>x.map((v,i)=>v+y[i]),neg=x=>x.map(v=>-v);
const one=[1,0,0,0,0],aV=[0,1,0,0,0],bV=[0,0,1,0,0],xV=[0,0,0,1,0],yV=[0,0,0,0,1];
function residual([b,z],[c,w]){
 if(b>c)return residual([c,w],[b,z]);
 let d=plus(w,neg(z));
 if(b===c)return b===0&&(same(d,aV)||same(d,neg(aV)))||b===3&&(same(d,bV)||same(d,neg(bV)));
 return b===1&&c===2&&same(d,neg(one))||b===1&&c===4&&same(d,xV)||b===2&&c===4&&same(d,yV);
}
for(let [name,{D,B,O}]of Object.entries(C)){
 const ports=D.flatMap(([b,z])=>[[b,z],[(b+1)%5,b===4?plus(z,one):z]]),m=D.length;
 ok(new Set(B.flat()).size===2*m&&B.length===m,"ports form perfect matching");
 let A=[];
 for(let [u,v]of B){ok(residual(ports[u],ports[v]),"literal symbolic edge "+name);A[u]=v;A[v]=u;}
 for(let order of O){
  let L=[...order].map(Number),P=[];
  ok(L.length===m&&new Set(L).size===m,"cut order permutation");
  for(let i=0;i<m;i++){let u=2*L[i]+1,v=2*L[(i+1)%m];P[u]=v;P[v]=u;}
  let V=[0];for(let i=1;i<m;i++)V.push(A[P[V.at(-1)]]);
  ok(new Set(V).size===m,"connected cut/rejoin "+name+order);
 }
}
function plan(n,a,b,x,y){
 let M=v=>(v%n+n)%n;
 function flip(){[a,b]=[b,a];[x,y]=[M(-1-y),M(-1-x)];}
 const P=(c,o)=>[c,o,a,b,x,y];
 if(y>=b&&y<n-b)flip();
 if(x>=a&&x<n-a)return P("P","0312");
 // Regard x,y in [-a,a-1] and [-b,b-1], respectively.
 let sx=x>=n-a?x-n:x,sy=y>=n-b?y-n:y;
 if(sy!==-1&&sy!==b-1){flip();sx=x>=n-a?x-n:x;sy=y>=n-b?y-n:y;}
 if(sx!==0&&sx!==-a)return P("Q",sx>0?(sx===1?"402315":"023154"):(sx===1-a?"305412":"054123"));
 if(sx===0&&sy===-1){
  if(a===1&&b>=2)flip();
  if(a>=2)return P("R","054123");
  return P("T","20473561");
 }
 if(sx===-a&&sy===-1)flip();
 if(x===0&&y===b-1){
  if(b>=2)return P("S","043512");
  flip();return P("T","20734651");
 }
 if(a===1&&x===n-1&&y===n-1)return P("T","20734651");
 ok(x===n-a&&y===b-1,"remaining endpoints");
 if(a!==b){
  if(a>b)flip();
  if(2*a+b-1<n)return P("R","032451");
  flip();return P("R","024153");
 }
 if(a===1)return P("T","73046521");
 return 3*a<=n?P("U","03462517"):P("V","03526174");
}
let count=0;
for(let n=5;n<=31;n+=2)for(let a=1;2*a<n;a++)for(let b=1;2*b<n;b++)for(let x=0;x<n;x++)for(let y=0;y<n;y++){
 let [c,o,A,B,X,Y]=plan(n,a,b,x,y),v=[1,A,B,X,Y];
 let T=C[c].D.map(([r,z],i)=>[5*((z.reduce((s,t,k)=>s+t*v[k],0)%n+n)%n)+r,i]);
 T.sort((a,b)=>a[0]-b[0]);ok(new Set(T.map(x=>x[0])).size===T.length&&T.map(x=>x[1]).join("")===o,"claimed order "+[n,a,b,x,y,c,o]);
 count++;
}
console.log("All symbolic port matchings and cut orders valid; finite order-regression count",count);
