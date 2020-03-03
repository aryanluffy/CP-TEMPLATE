#include <bits/stdc++.h>
#define lli long long int
#define pb push_back
#define mod 1000000007
#pragma GCC optimize ("-O3")
#define mod2 998244353
#define MAXN 1000000000
#define v32 vector<int>
#define v64 vector<lli>
#define v1024 vector <vector <int>>
#define v4096 vector <vector <lli>>
#define vt vector
#define f(x, y, z) for (lli x = y; x < z; x++)
#define fd(x, y, z) for (lli x = y; x > z; x--)
#define lb lower_bound
#define ld long double
#define m64 map<lli,lli>
#define m32 map<int,int>
#define m64it map<lli,lli>::iterator
#define m32it map<int,int>::iterator
#define fastio ios_base::sync_with_stdio(0);cin.tie(0);cout.tie(0)
#define ist insert
#define endl "\n"
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#define ordered_set tree<int, null_type,less<int>, rb_tree_tag,tree_order_statistics_node_update> 
#define p_q priority_queue 
#define min_p_q priority_queue <int,vt <int>,greater <int>>
using namespace std;
using namespace __gnu_pbds; 
template <typename T> 
void DEBUG_ARR(vt<T> a,char c)
{
	f(i,0,a.size())cout<<a[i]<<c;
	cout<<"\n";
}

lli tmod(lli x,lli m){return (x%m+m)%m;}//USE AT YOUR OWN RISK
lli power(lli x, lli y) 
{
    lli res = 1;  
   
    while (y > 0) 
    { 
        if (y & 1) 
            res = (res*x)%mod; 
        y = y>>1; 
        x = (x*x)%mod;  
    }
    if(res<0)
       res+=mod; 
    return res; 
}
//build function
//supports update and query 
class merge_sort_tree
{
  public:
	struct node
    {
      int l,r;
      ordered_set mp;
    };
	v32 a;
    vt <node> st; 
	
    merge_sort_tree(v32 b){
        a=b;
        st.resize(4*a.size());
        build(0,a.size()-1);
    }
    void build(int l,int r,int k=0){
        st[k].l=l,st[k].r=r;
        if(l==r){
            st[k].mp.insert(a[l]);
            return;
        }
        f(i,l,r+1)st[k].mp.insert(a[i]);
        build(l,(l+r)/2,2*k+1);
        build((l+r)/2+1,r,2*k+2);
    }
    void update(int id,int orig,int val,int k=0){
        int l=st[k].l,r=st[k].r;
        if(id<l || id>r) return;
        if(l==id && id==r){
            st[k].mp.erase(orig);
            st[k].mp.insert(val);
            return;
        }
        st[k].mp.erase(orig);
        st[k].mp.insert(val);
        update(id,orig,val,2*k+1);
        update(id,orig,val,2*k+2);
    }
    int query(int l,int r,int upper,int k=0){
        if(l>r)return 0;
        int ll=st[k].l,rr=st[k].r;
        if(r<ll || rr<l) return 0;
        if(l<=ll && rr<=r){
            return st[k].mp.order_of_key(upper);
        }
        return query(l,r,upper,2*k+1)+query(l,r,upper,2*k+2);   
    }
};

int main() 
{ 
    fastio;
    
    return 0; 	
}
