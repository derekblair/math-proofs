const U=[[0,1,2,3],[0,2,1,3],[0,3,1,2],[0,2,3,1],[0,1,3,2],[0,3,2,1]];
function Test(O,R,l,m){let P=[],Q=[],A=[],B=[];
function merge(T,sgn,blk){let Q=T.map(i=>i+4);return blk?(sgn?Q.concat(T):T.concat(Q)):T.flatMap(i=>sgn?[i+4,i]:[i,i+4]);}
function pair(C,x,y){C[x]=y;C[y]=x;}
function caps(C,ts,delta,sgn,blk){let L=merge(ts,sgn,blk);for(let j=0;j<L.length;j++)pair(C,L[j]+delta,L[(j+1)%L.length]);}
caps(A,[0,2],1,l&1,m&1);caps(B,[0,1],2,l&2,m&2);
function rolls(O,i,sgn,blk){let S=merge(O,sgn,blk);let C=[];for(let j=0;j<8;j++)C[S[j]]=S[(j+8+i)%8];return C;}
for(let u of [-1,1])for(let v of [-1,1]){P=rolls(O,u,l&4,m&4);Q=rolls(R,v,l&8,m&8);let Z=P.map(i=>Q[i]),W=[];Z.forEach((x,i)=>W[x]=i);let j=0,n=0;do{j=W[B[Z[A[j]]]];n++;}while(j!==0);if(n===4)return [u,v]}}

const normal=[[0,1,2,3],[0,3,2,1]], alternate=[[0,2,1,3],[0,3,1,2]];
for(const [m,bank] of [[1,normal],[2,alternate]])for(const O of bank)for(const R of bank){
 const actual=Test(O,R,0,m),exp=O===R?-1:1;
 if(!actual||actual[0]!==-1||actual[1]!==exp)throw Error([m,O,R,actual]);
}
function full(p,a,b,d,e,h,u,v,types) {
 const M=x=>(x%p+p)%p,I=(j,s)=>6*M(s)+types[j];
 const S=[0,a,b,a+b,h,h+a,h+b,h+a+b];
 if(new Set(S.map(M)).size!==8)throw Error("not eight sheets");
 const P=u<0?d:0,Q=v<0?e:0;
 const G=Array.from({length:6*p},()=>new Set());
 function add(u,v){if(u===v||G[u].has(v))throw Error("edge");G[u].add(v);G[v].add(u);}
 function drop(u,v){if(!G[u].delete(v)||!G[v].delete(u))throw Error("missing");}
 for(let s=0;s<p;s++) {
   add(I(0,s),I(0,s+a));add(I(5,s),I(5,s+b));
   add(I(1,s),I(2,s));add(I(1,s),I(2,s+d));
   add(I(3,s),I(4,s));add(I(3,s),I(4,s+e));
 }
 for(let c of [0,b,h,h+b])drop(I(0,c),I(0,c+a));
 for(let c of [0,a,h,h+a])drop(I(5,c+P+Q),I(5,c+P+Q+b));
 for(let c of S){
   drop(I(1,c),I(2,c+P));drop(I(3,c+P),I(4,c+P+Q));
   add(I(0,c),I(1,c));add(I(2,c+P),I(3,c+P));add(I(4,c+P+Q),I(5,c+P+Q));
 }
 if(G.some(E=>E.size!==2))throw Error("degree");
 let L=[0],seen=new Set([0]);
 while(L.length)for(let w of G[L.pop()])if(!seen.has(w)){seen.add(w);L.push(w);}
 if(seen.size!==6*p)throw Error([p,a,b,d,e,h,u,v,types,"connect"]);
}
// Force h=1, epsilon=1/80, and choose role steps by the desired inverse intervals.
// Retain only those actual primes/parameters meeting the analytic margins of the theorem.
const p=1009,inv=[0],M=x=>(x%p+p)%p;
for(let k=1;k<p;k++)for(let l=1;l<p;l++)if(M(k*l)===1){inv[k]=l;break;}
let count=0,classes=new Map;
for(let m of [1,2])for(let r=13;r<38;r++)for(let t=493;t<517;t++){
 let a=inv[m===1?t:r],b=inv[m===1?r:t];
 let tail=m===1?M(b*inv[a]):M(a*inv[b]);
 let other=m===1?M(a*inv[b]):M(b*inv[a]);
 if(!(80*tail>4*p&&80*tail<36*p&&80*Math.min(other,p-other)>4*p))continue;
 const S=[0,a,b,M(a+b)];
 for(let x=13;x<38;x++)for(let y=13;y<38;y++){
  function order(k){
   let W=S.map(z=>M(z*k)),L=[0,1,2,3].sort((i,j)=>W[i]-W[j]);
   if(L.some((i,j)=>80*M(W[L[(j+1)%4]]-W[i])<=4*p))return;
   return L.join("");
  }
  const O=order(x),R=order(y),bank=m===1?normal:alternate;
  if(!bank.some(w=>w.join("")===O)||!bank.some(w=>w.join("")===R))continue;
  const key=m+":"+O+":"+R;
  if((classes.get(key)||0)>=75)continue;
  classes.set(key,1+(classes.get(key)||0));
  for(let types of [[0,1,5,4,2,3],[0,1,3,2,5,4]])full(p,a,b,inv[x],inv[y],1,-1,O===R?-1:1,types);
  count++;
 }
}
console.log(count,[...classes]);
