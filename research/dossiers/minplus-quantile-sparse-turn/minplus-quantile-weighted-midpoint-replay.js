'use strict';
function getArms(a,L,R,minima){
 const cuts=[L,...minima.filter(i=>L<i&&i<=R),R+1], arms=[];
 const firstNonzero=(l,r)=>{for(let i=l;i<r;i++){const d=a[i+1]-a[i];if(d)return Math.sign(d);}return 0;};
 for(let j=0;j+1<cuts.length;j++){
   const lo=cuts[j],hi=cuts[j+1]-1;
   let x=lo,y=hi;
   while(x<y){const m=(x+y)>>1;if(firstNonzero(m,hi)>0)x=m+1;else y=m;}
   arms.push({lo,hi:x,forward:true});
   if(x<hi)arms.push({lo:x+1,hi,forward:false});
 }
 return arms;
}
const idx=(t,k)=>t.forward?t.lo+k:t.hi-k;
const length=t=>t.hi-t.lo+1;
function lower(a,t,l,r,p,weak){
 while(l<r){const m=(l+r)>>1,v=a[idx(t,m)];if(v<p||(weak&&v===p))l=m+1;else r=m;}
 return l;
}
function kthScore(a,arms,k){
 const active=arms.map(t=>[0,length(t)]);
 let steps=0;
 for(;;){
   let tot=0;const mids=[];
   for(let i=0;i<arms.length;i++){const [l,r]=active[i];if(l<r){const n=r-l;tot+=n;mids.push([a[idx(arms[i],l+Math.floor((n-1)/2))],n]);}}
   if(!tot||k<1||k>tot)throw Error("empty rank");
   mids.sort((x,y)=>x[0]-y[0]);let weight=0,p;
   for(const [v,m] of mids){weight+=m;if(2*weight>=tot){p=v;break;}}
   const bs=arms.map((t,i)=>{const [l,r]=active[i];return [lower(a,t,l,r,p,false),lower(a,t,l,r,p,true)];});
   let less=0,eq=0;for(let i=0;i<arms.length;i++){less+=bs[i][0]-active[i][0];eq+=bs[i][1]-bs[i][0];}
   steps++;
   if(k>less&&k<=less+eq)return [p,steps];
   if(k<=less){if(4*less>3*tot)throw Error("pivot reduction left");for(let i=0;i<arms.length;i++)active[i][1]=bs[i][0];}
   else {if(4*(tot-less-eq)>3*tot)throw Error("pivot reduction right");k-=less+eq;for(let i=0;i<arms.length;i++)active[i][0]=bs[i][1];}
 }
}
function kthLex(a,arms,k){
 const [p,steps]=kthScore(a,arms,k);
 let lesser=0;const ties=[];
 for(const t of arms){
   const l=lower(a,t,0,length(t),p,false),r=lower(a,t,0,length(t),p,true);
   lesser+=l;
   if(l<r)ties.push([Math.min(idx(t,l),idx(t,r-1)),r-l]);
 }
 k-=lesser;ties.sort((x,y)=>x[0]-y[0]);
 for(const [i,l]of ties){if(k<=l)return [p,i+k-1,steps];k-=l;}
 throw Error("ties not found");
}
function minimaOf(a){
 const ans=[];let i=0;
 while(i<a.length){let r=i+1;while(r<a.length&&a[r]===a[i])r++;
   if(i>0&&r<a.length&&a[i-1]>a[i]&&a[r]>a[i])ans.push(i);
   i=r;
 } return ans;
}
let profiles=0,ranges=0,ranked=0,stepsMax=0;
function test(a){
 const valley=minimaOf(a);profiles++;
 for(let l=0;l<a.length;l++)for(let r=l;r<a.length;r++){
   const arms=getArms(a,l,r,valley),flat=arms.flatMap(t=>Array.from({length:length(t)},(_,j)=>idx(t,j))).sort((x,y)=>x-y);
   if(flat.length!==r-l+1||flat.some((x,j)=>x!==l+j))throw Error("partition");
   for(const t of arms)for(let j=1;j<length(t);j++)if(a[idx(t,j-1)]>a[idx(t,j)])throw Error("arm");
   const expected=flat.map(j=>[a[j],j]).sort((x,y)=>x[0]-y[0]||x[1]-y[1]);ranges++;
   for(let k=1;k<=expected.length;k++){
    const [p,j,it]=kthLex(a,arms,k),[ep,ej]=expected[k-1];if(p!==ep||j!==ej)throw Error("rank");
    ranked++;stepsMax=Math.max(stepsMax,it);
   }
 }
}
function rec(v,n){
 test(v);if(v.length===n)return;
 for(const x of [-1,0,1])rec([...v,v.at(-1)+x],n);
}
rec([0],8);
console.log(JSON.stringify({profiles,ranges,ranked,stepsMax}));