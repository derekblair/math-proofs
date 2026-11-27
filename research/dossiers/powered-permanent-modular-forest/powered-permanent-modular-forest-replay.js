
/* Exact replay of the modular-potential forest bound on subdivided powered permanents. */
function check(condition, message) {
  if (!condition) throw new Error(message);
}
function graph(n, powers) {
  let order = n;
  const edges = [];
  const paths = [];
  for (let row = 0; row < n; row++) for (let col = 0; col < n; col++) {
    const label = row*n+col;
    const length = powers[label];
    let left = row;
    const active = [];
    const inactive = [];
    for (let j = 1; j < length; j++) {
      const internal = order++;
      active.push({left,right:internal,label});
      inactive.push({left:internal,right:internal,label:-1});
      left = internal;
    }
    active.push({left,right:col,label});
    edges.push(...active,...inactive);
    paths.push({active,inactive});
  }
  return {paths,edges,order};
}
function lift(n, paths, permutation) {
  return paths.flatMap(({active,inactive},label) =>
    permutation[Math.floor(label/n)] === label%n ? active : inactive);
}
function confirm(n,powers,reference) {
  const {paths,edges,order}=graph(n,powers);
  check(order===n+powers.reduce((s,q)=>s+q-1,0),"wrong construction order");
  const matched = lift(n,paths,reference);
  check(matched.length===order,"reference shape");
  check(new Set(matched.map(e=>e.left)).size===order,"reference left");
  check(new Set(matched.map(e=>e.right)).size===order,"reference right");
  const vertices=Array.from({length:order},()=>[]);
  const owner=[];
  for (const edge of matched) owner[edge.right]=edge.left;
  for (const {left,right,label} of edges) {
    vertices[left].push({to:owner[right],label,step:1});
    vertices[owner[right]].push({to:left,label,step:-1});
  }
  const refLabels=new Set(matched.map(e=>e.label));
  const variables=powers.map((_,i)=>i).filter(i=>!refLabels.has(i));
  const treeCounts=Array(powers.length).fill(0);
  const potentials=Array(order);
  let components=0;
  for (let root=0;root<order;root++) {
    if (potentials[root]!==undefined) continue;
    ++components;
    potentials[root]=Array(powers.length).fill(0);
    const todo=[root], ranges=new Map(variables.map(label=>[label,new Set([0])]));
    for (let i=0;i<todo.length;i++) {
      const vertex=todo[i];
      for (const {to,label,step} of vertices[vertex]) {
        const pot=potentials[vertex].slice();
        if (label>=0 && !refLabels.has(label)) pot[label]=(pot[label]+step+powers[label])%powers[label];
        if (potentials[to]===undefined) {
          potentials[to]=pot;
          todo.push(to);
          if (label>=0 && !refLabels.has(label)) ++treeCounts[label];
          for (const variable of variables) ranges.get(variable).add(pot[variable]);
        } else {
          check(potentials[to].every((x,k)=>x===pot[k]),"modular potential mismatch");
        }
      }
    }
    if (components===1 && todo.length===order) for (const variable of variables) {
      check(ranges.get(variable).size===powers[variable],"coordinate does not visit every residue");
    }
  }
  check(components===1,"subdivision should have connected contraction");
  for (const variable of variables) {
    check(treeCounts[variable]>=powers[variable]-1,"forest count too small");
    const row=Math.floor(variable/n), col=variable%n;
    const chosen=reference.slice(), displaced=chosen.indexOf(col);
    [chosen[row],chosen[displaced]]=[chosen[displaced],chosen[row]];
    const alternate=lift(n,paths,chosen);
    check(new Set(alternate.map(e=>e.left)).size===order,"alternate left");
    check(new Set(alternate.map(e=>e.right)).size===order,"alternate right");
    check(alternate.filter(e=>e.label===variable).length===powers[variable],"alternate label");
  }
  return variables.length;
}

let cases=0, nonreferenceLabels=0;
for(let n=2;n<=8;n++) for(let q=2;q<=6;q++) for(let shift=0;shift<n;shift++){
  const ref=Array.from({length:n},(_,i)=>(i+shift)%n);
  for(const mixed of [false,true]){
    const powers=Array.from({length:n*n},(_,i)=>mixed?2+(q+i*13)%7:q);
    nonreferenceLabels+=confirm(n,powers,ref);
    cases++;
  }
}
console.log({cases,nonreferenceLabels});
