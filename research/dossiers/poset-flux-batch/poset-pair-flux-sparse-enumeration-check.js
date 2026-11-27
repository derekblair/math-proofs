let seed=729,R=()=>((seed=Math.imul(seed,1664525)+1013904223>>>0)/2**32),J=0,edges=0,cases=0;
for(let it=0;it<1600;it++){
 const n=3+it%8,w=1+it%Math.min(6,n),A=Array.from({length:w},()=>[]),D=Array(n).fill(0),chain=[];
 for(let v=0;v<n;v++){chain.push(v%w);A[v%w].push(v);}
 for(let j=1;j<n;j++)for(let i=0;i<j;i++)if(chain[i]===chain[j]||R()<.29)D[j]|=D[i]|1<<i;
 const need=D.map(mask=>A.map(c=>c.reduce((z,v,i)=>(mask>>v&1)?i+1:z,0)));
 let Z=[], map=new Map();
 function get(p){let k=p.join();if(map.has(k))return map.get(k);let v={p,out:[],F:0n,B:0n};map.set(k,v);Z.push(v);return v;}
 let start=get(Array(w).fill(0)); start.F=1n;
 for(let v of Z)for(let c=0;c<w;c++){
   let y=A[c][v.p[c]];if(y===undefined||need[y].some((v0,i)=>v0>v.p[i]))continue;
   let q=v.p.slice();q[c]++;let u=get(q);u.F+=v.F;v.out.push([u,y]);edges++;
 }
 Z.at(-1).B=1n;
 for(let i=Z.length-2;i>=0;i--)for(let [u] of Z[i].out)Z[i].B+=u.B;
 let T=Array.from({length:n},()=>A.map(c=>Array(c.length+1).fill(0n)));
 for(let v of Z)for(let [u,y] of v.out){let f=v.F*u.B;for(let c=0;c<w;c++){T[y][c][0]+=f;T[y][c][v.p[c]]-=f;}}
 let P=Array.from({length:n},()=>Array(n).fill(0n));
 for(let y=0;y<n;y++)for(let c=0;c<w;c++){let v=0n;for(let i=0;i<A[c].length;i++){v+=T[y][c][i];P[A[c][i]][y]=v;}}
 let I=0;for(let m=0;m<2**n;m++)if(D.every((d,i)=>!(m>>i&1)||!(d&~m)))I++;
 let E=0n,C=Array.from({length:n},()=>Array(n).fill(0n));function brute(m,L){if(L.length===n){E++;for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)C[L[i]][L[j]]++;return;}for(let x=0;x<n;x++)if(!(m>>x&1)&&!(D[x]&~m))brute(m|1<<x,[...L,x]);}brute(0,[]);
 if(Z.length!==I||start.B!==E||Z.at(-1).F!==E||P.some((row,i)=>row.some((x,j)=>x!==C[i][j])))throw Error("enumeration mismatch");
 J+=Z.length;cases++;
}
console.log({cases,J,edges});