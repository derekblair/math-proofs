from collections import deque
def generate(m,n):
    H=[set() for _ in range(4+4*m+2*n)]
    def link(a,b): H[a].add(b);H[b].add(a)
    link(0,1);link(2,3)
    for k in range(m):
        a=4+4*k
        for u,v in [(0,a),(3,a+1),(0,a+2),(3,a+3),(a,a+1),(a,a+2),(a+1,a+3)]:link(u,v)
    for k in range(n):
        a=4+4*m+2*k
        for u,v in [(1,a),(2,a+1),(a,a+1)]:link(u,v)
    return H
def distances(H):
    M=[]
    for i in range(len(H)):
        d={i:0};q=deque([i])
        while q:
            j=q.popleft()
            for k in H[j]-d.keys():d[k]=d[j]+1;q.append(k)
        M.append([d[j] for j in range(len(H))])
    return M
def dump(name,mat):
    print(f'def {name} : Array (Array Nat) := #[')
    for i,row in enumerate(mat):print('  #['+', '.join(map(str,row))+']'+(',' if i+1<len(mat) else ''))
    print(']')
if __name__=='__main__':
    H=generate(2,2);M=distances(H)
    K=[[next((k for k in H[j] if M[i][k]<M[i][j]),j) for j in range(len(H))] for i in range(len(H))]
    dump('distData',M);dump('predData',K)
