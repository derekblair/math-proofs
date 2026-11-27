"use strict";
const assert=require("node:assert/strict");
function perms(xs){return xs.length?xs.flatMap((x,i)=>perms(xs.filter((_,j)=>i!==j)).map(t=>[x,...t])):[[]];}
const P=perms([0,1,2,3]),index=new Map(P.map((p,i)=>[p.join(""),i]));
function swap(p,a,b){return p.map((v,i)=>i===a?p[b]:i===b?p[a]:v);}
function sign(p){let a=1;for(let i=0;i<4;i++)for(let j=i+1;j<4;j++)if(p[i]>p[j])a=-a;return a;}
const kinds=[[0,1,2,3],[0,2,1,3],[0,3,1,2]];
function pair(p,k){const [a,b,c,d]=k;return swap(swap(p,a,b),c,d);}
const cosets=new Map,clue=[];
for(const [i,p] of P.entries()){
 const key=[i,...kinds.map(k=>index.get(pair(p,k).join("")))].sort((a,b)=>a-b).join(",");
 if(!cosets.has(key))cosets.set(key,cosets.size);
 clue[i]=cosets.get(key);
}
assert.equal(cosets.size,6);
const inCosets=Array.from({length:6},(_,c)=>P.map((_,i)=>i).filter(i=>clue[i]===c));
const pSign=inCosets.map(ps=>sign(P[ps[0]]));
assert.deepEqual(pSign.slice().sort(),[-1,-1,-1,1,1,1]);
const vals=new Map;
function sig(i,j){
 const a=P[i],b=P[j];
 return a.flatMap((v,i)=>[i*4+v,i*4+b[i]]).sort((x,y)=>x-y).join(",");
}
for(let i=0;i<24;i++)for(let j=i+1;j<24;j++){
 const k=sig(i,j);if(!vals.has(k))vals.set(k,[]);vals.get(k).push([i,j]);
}
assert.equal([...vals.values()].filter(x=>x.length===1).length,240);
const rects=[...vals.values()].filter(x=>x.length>1).map(pairs=>{
 assert.equal(pairs.length,2);
 assert(pairs.every(([i,j])=>clue[i]===clue[j]));
 assert.notEqual(clue[pairs[0][0]],clue[pairs[1][0]]);
 assert.equal(sign(P[pairs[0][0]])*sign(P[pairs[0][1]]),sign(P[pairs[1][0]])*sign(P[pairs[1][1]]));
 return pairs.sort((a,b)=>pSign[clue[b[0]]]-pSign[clue[a[0]]]);
});
assert.equal(rects.length,18);
const adj=new Map;
for(const [a,b] of rects){
 assert.equal(pSign[clue[a[0]]],1);assert.equal(pSign[clue[b[0]]],-1);
 const k=clue[a[0]]+","+clue[b[0]];
 if(!adj.has(k))adj.set(k,[]);adj.get(k).push([a,b]);
}
assert.equal(adj.size,9);
for(const rows of adj.values()){
 assert.equal(rows.length,2);
 for(let j=0;j<2;j++)assert.equal(new Set(rows.flatMap(x=>x[j])).size,4);
}
const cert=[
 ["0123","0132","1023","1032"],["0123","0321","2103","2301"],["0132","0312","2130","2310"],
 ["0213","0231","2013","2031"],["0213","0312","1203","1302"],["0231","0321","1230","1320"],
 ["1023","1320","2013","2310"],["1032","1302","2031","2301"],["1203","1230","2103","2130"]
].map(r=>r.map(s=>index.get(s)).sort((a,b)=>a-b));
const canonical=r=>r.flat().sort((a,b)=>a-b).join(",");
for(const row of cert)assert(rects.some(r=>canonical(r)===canonical([row])));
assert.equal(cert.length%2,1);
for(let i=0;i<24;i++)assert.equal(cert.flat().filter(j=>i===j).length%2,0);
const pos=pSign.indexOf(1),neg=pSign.indexOf(-1),dirs=Array(24),eps=Array(24);let next=0;
for(const i of inCosets[pos]){dirs[i]=next;eps[i]=1;}next++;
for(const [_,[i,j]] of adj.get(pos+","+neg)){dirs[i]=dirs[j]=next;eps[i]=1;eps[j]=-1;}next++;
for(let c=0;c<6;c++)if(c!==pos&&c!==neg){
 const side=pSign[c]===1?0:1;const key=side===0?c+","+neg:pos+","+c;
 for(const rec of adj.get(key)){
  const [i,j]=rec[side],[x,y]=rec[1-side];
  dirs[i]=dirs[j]=next++;eps[i]=1;eps[j]=-eps[x]*eps[y];
 }
}
assert.equal(next,10);
const gram=(i,j)=>dirs[i]===dirs[j]?eps[i]*eps[j]:0;
for(let i=0;i<24;i++)assert.equal(gram(i,i),1);
for(const pairs of vals.values())assert.equal(pairs.reduce((v,[i,j])=>v+gram(i,j),0),0);
// Six fixed complex-mask squares: the mask phase per match is i once for each
// chosen top-left edge. The ordinary determinant sign is included in Gram.
const classes=new Map;
for(const [i,p] of P.entries()){
 const a=p.slice(0,2).sort((x,y)=>x-y),b=p.slice(2).sort((x,y)=>x-y),k=a.join("")+b.join("");
 if(!classes.has(k))classes.set(k,new Map);
 classes.get(k).set(i,Number(p[0]===a[0])+Number(p[2]===b[0]));
}
assert.equal(classes.size,6);
const maskGram=(i,j)=>[...classes.values()].reduce((v,M)=>{
 if(!M.has(i)||!M.has(j))return v;
 return v+sign(P[i])*sign(P[j])*[1,0,-1,0][(4+M.get(i)-M.get(j))%4];
},0);
for(let i=0;i<24;i++)assert.equal(maskGram(i,i),1);
for(const pairs of vals.values())assert.equal(pairs.reduce((v,[i,j])=>v+maskGram(i,j),0),0);
console.log({rectangles:rects.length,noncollidingOffDiagonal:240,cert,gramRank:next,complexMaskTerms:classes.size});
