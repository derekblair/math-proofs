function count(n,a,b,d,e){
 const mod=x=>(x%n+n)%n,abs=x=>Math.min(mod(x),mod(-x));
 const iv=x=>{let y=1;while(mod(x*y)!==1)y++;return y;};
 const S=[0,a,b,mod(a+b)], labels=new Set(S);if(labels.size!==4)throw Error();
 const B=new Set;
 const E=(i,j)=>[Math.min(i,j),Math.max(i,j)].join(",");
 for(let t=0;t<n;t++){
  if(t!==0&&t!==b)B.add(E(6*t,6*mod(t+a)));
  if(t!==0&&t!==a)B.add(E(6*t+3,6*mod(t+b)+3));
  if(!labels.has(t)){B.add(E(6*t+1,6*t+5));B.add(E(6*t+2,6*t+4));}
  B.add(E(6*t+1,6*mod(t+d)+5));B.add(E(6*t+2,6*mod(t+e)+4));
  if(labels.has(t)){B.add(E(6*t,6*t+1));B.add(E(6*t+2,6*t+3));B.add(E(6*t+4,6*t+5));}
 }
 const G=Array.from({length:6*n},()=>[]);
 for(let key of B){let [u,v]=key.split(",").map(Number);G[u].push(v);G[v].push(u);}
 if(G.some(v=>v.length!==2))throw Error("non-2-regular");
 let seen=new Set,k=0;
 for(let u=0;u<6*n;u++)if(!seen.has(u)){k++;let Q=[u];seen.add(u);for(let i=0;i<Q.length;i++)for(let v of G[Q[i]])if(!seen.has(v)){seen.add(v);Q.push(v);}}
 const s=(abs(a*iv(d))<abs(b*iv(d)))!==(abs(a*iv(e))<abs(b*iv(e)));
 if(k!==(s?1:2))throw Error("rank disagreement");
 return k;
}
let N=0,W=0;
for(let p of [5,7,11,13,17,19,23,29])for(let b=2;b<=(p-1)/2;b++)for(let d=1;d<p;d++)for(let e=1;e<p;e++){
 N++;if(count(p,1,b,d,e)===1)W++;
}
console.log({N,W,two:N-W});
