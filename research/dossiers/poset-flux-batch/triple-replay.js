let s=20261127;const R=()=>((s=Math.imul(s,1664525)+1013904223>>>0)>>>12)/2**20;
let cases=0,J=0,tuples=0;
for(let rep=0;rep<220;rep++){
 const n=2+rep%7,w=1+rep%Math.min(4,n),U=(1<<n)-1,p=Array(n).fill(0);
 const C=Array.from({length:w},(_,i)=>Array.from({length:n},(_,j)=>j).filter(j=>j%w===i));
 for(let y=0;y<n;y++)for(let x=0;x<y;x++)if(x%w===y%w||R()<.12+(rep%5)*.11)p[y]|=1<<x;
 const full=Array(U+1).fill(0n),B=full.slice(),edges=[];full[0]=1n;
 for(let I=0;I<=U;I++)if(full[I])for(let y=0;y<n;y++)if(!(I>>y&1)&&!(p[y]&~I)){
  let Q=I|1<<y;full[Q]+=full[I];edges.push([I,Q,y]);
 }
 B[U]=1n;for(let j=edges.length-1;j>=0;j--){const[I,Q]=edges[j];B[I]+=B[Q];}
 const ideals=Array.from({length:U+1},(_,i)=>i).filter(i=>full[i]);
 const idx=(x,y,z)=>(y*n+x)*n+z;
 const dense=Array(n**3).fill(0n),rect=dense.slice(),literal=dense.slice();
 for(const[I,Q,y]of edges)for(let x=0;x<n;x++)if(I>>x&1)for(let z=0;z<n;z++)
  if(z!==y&&!(I>>z&1))dense[idx(x,y,z)]+=full[I]*B[Q];
 const key=C.flat(),off=[0];for(const c of C)off.push(off.at(-1)+c.length);
 for(let y=0;y<n;y++){
  const D=Array.from({length:n+1},()=>Array(n+1).fill(0n));
  for(const[I,Q,k]of edges)if(k===y){
   for(let a=0;a<w;a++)for(let b=0;b<w;b++){
    let xl=off[a],xh=xl+C[a].filter(x=>I>>x&1).length;
    let zl=off[b]+C[b].filter(z=>Q>>z&1).length,zh=off[b+1],v=full[I]*B[Q];
    D[xl][zl]+=v;D[xh][zl]-=v;D[xl][zh]-=v;D[xh][zh]+=v;
   }
  }
  for(let i=0;i<n;i++)for(let j=0;j<n;j++){
   D[i][j]+=(i?D[i-1][j]:0n)+(j?D[i][j-1]:0n)-(i&&j?D[i-1][j-1]:0n);
   rect[idx(key[i],y,key[j])]=D[i][j];
  }
 }
 function go(I,L){
  if(I===U){for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)for(let c=b+1;c<n;c++)literal[idx(L[a],L[b],L[c])]++;return;}
  for(let y=0;y<n;y++)if(!(I>>y&1)&&!(p[y]&~I))go(I|1<<y,[...L,y]);
 }
 go(0,[]);if(dense.some((x,i)=>x!==literal[i]||x!==rect[i]))throw Error("triple mismatch");
 cases++;J+=ideals.length;tuples+=n**3;
}
console.log({cases,J,tuples});
