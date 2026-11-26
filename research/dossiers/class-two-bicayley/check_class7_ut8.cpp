#include <array>
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <random>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using Mat=std::array<std::array<int,8>,8>;
int p;
Mat one() { Mat m={}; for(int i=0;i<8;i++)m[i][i]=1; return m; }
Mat mul(Mat a,Mat b) {
 Mat m=one();
 for(int i=0;i<8;i++)for(int j=i+1;j<8;j++){
   int v=0;for(int k=i;k<=j;k++)v+=a[i][k]*b[k][j];
   m[i][j]=v%p;
 }
 return m;
}
Mat inv(Mat m) {Mat r=one(); for(int i=0;i<p-1;i++)r=mul(r,m); assert(mul(m,r)==one()); return r;}
Mat elem(std::array<int,7> t) {
  Mat r=one();for(int i=0;i<7;i++)r[i][i+1]=t[i]; return r;
}
Mat rim[2][2];
const int Back[3]={1,0,2};
struct Vert { int b; Mat m; };
using Key=unsigned __int128;
struct KeyHash { size_t operator()(Key k)const {return uint64_t(k) ^ (uint64_t(k >> 64)*0x9e3779b97f4a7c15ULL);}};
Key key(Vert x) {
 Key s=x.b;
 for(int i=0;i<8;i++)for(int j=i+1;j<8;j++)s=s*p+x.m[i][j];
 return s;
}
Vert step(Vert v,int port) {if(port==2)return {1-v.b,v.m};return {v.b,mul(v.m,rim[v.b][port])};}
std::unordered_multimap<Key,uint64_t,KeyHash> hits;
std::vector<Key> path;
bool dfs(Vert v,int last,int len,uint64_t w,int root) {
 if(!len){
   auto k=path.back(); auto it=hits.equal_range(k);
   for(auto i=it.first;i!=it.second;i++){
     auto other=i->second;
     bool sep=true;
     Vert z={root,one()};
     for(int t=0;t<(int)path.size()-2;t++){
       z=step(z,other%3); other/=3;
       if(std::find(path.begin()+1,path.end()-1,key(z))!=path.end()-1){sep=false;break;}
     }
     if(sep)return true;
   }
   uint64_t rev=0;for(int i=0;i<(int)path.size()-1;i++){rev=rev*3+w%3;w/=3;}
   hits.emplace(k,rev);
   return false;
 }
 for(int j=0;j<3;j++)if(last<0||Back[last]!=j){
   Vert z=step(v,j); Key k=key(z);
   if(std::find(path.begin(),path.end(),k)!=path.end())continue;
   path.push_back(k);
   if(dfs(z,j,len-1,w*3+j,root)) return true;
   path.pop_back();
 }
 return false;
}
bool blocks(int h,int b) {
 hits.clear();path={key({b,one()})};
 return dfs({b,one()},-1,h,0,b);
}
bool word(std::string s,int r=0) {
 Vert v={r,one()};std::vector<Key> seen{key(v)};
 for(int i=0;i<(int)s.size();i++){
   v=step(v,s[i]-'0');auto k=key(v);
   if(i==(int)s.size()-1)return k==seen[0];
   if(std::find(seen.begin(),seen.end(),k)!=seen.end())return false;
   seen.push_back(k);
 }
 return false;
}


int main() {
 p=17;
 for(int a=1;a<p;a++)for(int b=0;b<p;b++){
 rim[0][0]=elem({4,4,4,10,7,1,a});rim[0][1]=inv(rim[0][0]);
 rim[1][0]=elem({12,12,9,12,2,0,b});rim[1][1]=inv(rim[1][0]);
 if(!word("12120021212021202002121212020021121202120202112020021121202020211202020211212021202021120200212121202002112120021212021202002112"))continue;
 Vert z={0,one()}; for(const char c:std::string("1212002121202120200212121202002112120212020211202002112120202021"))z=step(z,c-'0');
 if(z.m[0][7]==0)continue;
 std::cout<<"positive exact candidate a,b "<<a<<" "<<b<<", selected seventh residue "<<z.m[0][7]<<"\n";
 for(int h:{2,4,8,16})for(int b:{0,1}){
   assert(!blocks(h,b));
   std::unordered_set<Key,KeyHash> endpoints;
   for(const auto &entry : hits) endpoints.insert(entry.first);
   assert(endpoints.size()==hits.size());
   std::cout<<h<<" "<<b<<" distinct short endpoints "<<endpoints.size()<<"\n";
 }
 assert(word("1121202120202112020021121202020212120021212021202002121212020021",1));
 std::cout<<"Also has an explicit C64\n";
 return 0;
 }
 return 2;
}
