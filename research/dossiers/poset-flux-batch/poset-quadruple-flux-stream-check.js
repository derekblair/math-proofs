let seed=742,R=()=>((seed=Math.imul(seed,1664525)+1013904223>>>0)/2**32),cases=0,keys=0,arcs=0,flows=0;
for(let t=0;t<480;t++){
 let n=4+t%5,w=1+t%Math.min(4,n),C=Array.from({length:w},()=>[]),D=Array(n).fill(0);
 for(let i=0;i<n;i++)C[i%w].push(i);
 for(let j=1;j<n;j++)for(let i=0;i<j;i++)if(i%w===j%w||R()<.29)D[j]|=D[i]|1<<i;
 let N=(1<<n)-1,F=Array(N+1).fill(0n),B=F.slice(),adj=Array.from({length:N+1},()=>[]),E=[];F[0]=B[N]=1n;
 for(let I=0;I<N;I++)if(F[I])for(let y=0;y<n;y++)if(!(I>>y&1)&&!(D[y]&~I)){let K=I|1<<y;F[K]+=F[I];adj[I].push([K,y]);E.push([I,K,y]);}
 for(let I=N-1;I>=0;I--)for(let [J] of adj[I])B[I]+=B[J];

 let out=Array(n**4).fill(0n),idx=(x,y,z,t)=>((x*n+y)*n+z)*n+t;
 for(let x=0;x<n;x++)for(let y=0;y<n;y++){
  let G=Array(N+1).fill(0n),V=Array.from({length:n},()=>C.map(c=>Array(c.length+1).fill(0n)));
  for(let [I,S,z] of E){
   if(z===y){if(I>>x&1)G[S]+=F[I];continue;}
   G[S]+=G[I];
   if(G[I]){
    let k=G[I]*B[S];flows++;
    for(let c=0;c<w;c++){let q=C[c].filter(i=>S>>i&1).length;V[z][c][q]+=k;}
   }
  }
  for(let z=0;z<n;z++)for(let c=0;c<w;c++){
   let f=0n;for(let i=0;i<C[c].length;i++){f+=V[z][c][i];out[idx(x,y,z,C[c][i])]=f;}
  }
 }
 let literal=Array(n**4).fill(0n);
 function walk(I,L){if(I===N){for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)for(let c=b+1;c<n;c++)for(let d=c+1;d<n;d++)literal[idx(L[a],L[b],L[c],L[d])]++;return;}
 for(let [J,y] of adj[I])walk(J,[...L,y]);}walk(0,[]);
 if(out.some((x,i)=>x!==literal[i]))throw Error("quad result");
 cases++;keys+=n**4;arcs+=E.length;
}
console.log({cases,keys,arcs,flows});
