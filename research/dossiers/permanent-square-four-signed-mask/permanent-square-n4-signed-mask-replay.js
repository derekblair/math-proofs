"use strict";
const I=[0,1,2,3], V=[[0,1,2,3],[1,0,3,2],[2,3,0,1],[3,2,1,0]];
function perms(prefix){return prefix.length===4?[prefix]:I.filter(v=>!prefix.includes(v)).flatMap(v=>perms([...prefix,v]));}
const P=perms([]),str=p=>p.join(""),idx=x=>P.findIndex(y=>str(y)===str(x));
const tag=p=>V.map(q=>str(q.map(x=>p[x]))).sort()[0];
const G=[...new Set(P.map(tag))].map(g=>P.map((p,i)=>tag(p)===g?i:-1).filter(i=>i>=0));
const id=P.map((p,i)=>G.findIndex(g=>g.includes(i)));
const rectangles=[];
const sw=(p,a,b)=>p.map((v,i)=>i===a?p[b]:i===b?p[a]:v);
for(let i=0;i<P.length;i++)for(const [a,b,c,d] of [[0,1,2,3],[0,2,1,3],[0,3,1,2]]){
 const s=[i,idx(sw(sw(P[i],a,b),c,d)),idx(sw(P[i],a,b)),idx(sw(P[i],c,d))];
 const key=[...s].sort((x,y)=>x-y).join();
 if(!rectangles.some(r=>r.key===key))rectangles.push({s,key});
}

const certificate=[
"0123 0132 1023 1032","0123 0321 2103 2301","0132 0312 2130 2310",
"0213 0231 2013 2031","0213 0312 1203 1302","0231 0321 1230 1320",
"1023 1320 2013 2310","1032 1302 2031 2301","1203 1230 2103 2130"];
const R=certificate.map(line=>{const k=line.split(" ").map(x=>P.findIndex(p=>str(p)===x)).sort((a,b)=>a-b).join();
 return rectangles.find(r=>r.key===k).s;
});
function sorted(m){return [...m].sort((a,b)=>a-b);}
function pairing(g,other) {
 const pairs=rectangles.filter(({s})=>s.some(i=>id[i]===g)&&s.some(i=>id[i]===other))
   .map(({s})=>s.filter(i=>id[i]===g));
 if(pairs.length!==2||new Set(pairs.flat()).size!==4)throw Error("pairing");
 return pairs.map(x=>sorted(x).join()).sort().join("|");
}
const sides=G.map(g=>P[g[0]].reduce((s,x,i)=>s+P[g[0]].slice(i+1).filter(y=>y<x).length,0)%2);
for(let g=0;g<6;g++){
 const opp=I.concat([4,5]).filter(j=>sides[j]!==sides[g]);
 if(new Set(opp.map(j=>pairing(g,j))).size!==3)throw Error("three distinct pairings");
}
const incidence=P.map((_,i)=>R.filter(s=>s.includes(i)).length);
if(incidence.some(x=>x%2))throw Error("odd-nine even incidence");
if(new Set(R.map(s=>sorted([id[s[0]],id[s[2]]]).join())).size!==9)
 throw Error("one rectangle per edge");
for(let g=0;g<6;g++){
 const originals=R.map(s=>s.filter(i=>id[i]===g)).filter(x=>x.length);
 if(originals.length!==3||new Set(originals.flat()).size!==3)throw Error("triangle");
 const excluded=new Set();
 for(const shift of V){
  const triangles=new Set(originals.flat().map(j=>idx(shift.map(u=>P[j][u]))));
  if(triangles.size!==3||[...triangles].some(j=>id[j]!==g))throw Error("coset action");
  excluded.add(G[g].find(i=>!triangles.has(i)));
 }
 if(excluded.size!==4)throw Error("all triangles negative");
}
const few=[];
for(let a=0;a<=3;a++)for(let b=0;b<=3;b++){
 const min=a+b+(3-a)*(b>=2?3:2)+(3-b)*(a>=2?3:2);
 if(min<=10)few.push([a,b,min]);
}
if(JSON.stringify(few)!=="[[1,1,10],[1,3,10],[2,2,10],[2,3,8],[3,1,10],[3,2,8],[3,3,6]]")
 throw Error("rank budget");
const left=["0132","0213","0321"],right=["0123","0231","0312"];
function edgeCount(labels){
 return I.map(i=>labels.map(p=>p[i]).sort().join("")).join(";");
}
if(edgeCount(left)!==edgeCount(right))throw Error("cubic matching monomials");
for(const [group,anchor] of [[0,"0123"],[1,"0132"]]){
 const j=P.findIndex(p=>str(p)===anchor);
 if(id[j]!==group||!R.some(s=>s.includes(j)&&s.some(i=>id[i]!==0&&id[i]!==1)))
  throw Error("anchor has a nonmissing link");
}
let signAssignments=0,feasibleAssignments=0;
for(let missing=0;missing<6;missing++){
 const known=G.flatMap((g,i)=>i===missing?[]:g.slice(1));
 const lookup=P.map((_,i)=>known.indexOf(i));
 for(let mask=0;mask<1<<known.length;mask++){
  signAssignments++;
  const S=P.map((_,i)=>lookup[i]>=0&&(mask&(1<<lookup[i]))?-1:1);
  const H=Array.from({length:4},()=>Array(4).fill(1));
  let ok=true;
  for(const {s:[a,b,c,d]} of rectangles){
   if(id[a]===missing){const x=G[missing].indexOf(a),y=G[missing].indexOf(b);H[x][y]=H[y][x]=-S[c]*S[d];}
   else if(id[c]===missing){const x=G[missing].indexOf(c),y=G[missing].indexOf(d);H[x][y]=H[y][x]=-S[a]*S[b];}
   else if(S[a]*S[b]!==-S[c]*S[d]){ok=false;break;}
  }
  if(!ok)continue;
  feasibleAssignments++;
  for(let i=0;i<4;i++)for(let j=i+1;j<4;j++)for(let k=j+1;k<4;k++){
   if(H[i][j]*H[i][k]*H[j][k]!==-1)throw Error("triangle must be negative");
  }
 }
}

const coefficientPairs=new Map();
for(let i=0;i<24;i++)for(let j=i+1;j<24;j++){
 const key=I.map(k=>[P[i][k],P[j][k]].sort().join("")).join(";");
 if(!coefficientPairs.has(key))coefficientPairs.set(key,[]);
 coefficientPairs.get(key).push([i,j]);
}
let uniquePairs=0,doubleCollisions=0;
for(const pairs of coefficientPairs.values()){
 if(pairs.length===1&&id[pairs[0][0]]!==id[pairs[0][1]])uniquePairs++;
 else if(pairs.length===2&&pairs.every(([a,b])=>id[a]===id[b]))doubleCollisions++;
 else throw Error("unexpected coefficient-pair multiplicity");
}
if(uniquePairs!==240||doubleCollisions!==18)throw Error("coefficient index counts");
console.log(JSON.stringify({uniquePairs,doubleCollisions,rectangles:rectangles.length,oddCertificate:R.length,cosets:G.map(g=>g.map(i=>str(P[i]))),budget:few,signAssignments,feasibleAssignments,cubic:{left,right,edgeLists:edgeCount(left)}}));
