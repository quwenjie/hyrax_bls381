#define DEBUG
#include <iostream>
#include <vector>
#include <mcl/bls12_381.hpp>
#include "timer.hpp"
using namespace std;
using namespace mcl::bn;

inline G1 perdersen_commit(G1* g,Fr* f,int n)
{
    G1 ret;
    G1::mulVec(ret,g,f,n);
    return ret;
}
Fr lagrange(Fr *r,int l,int k)
{
    assert(k>=0 && k<(1<<l));
    Fr ret=1;
    for(int i=0;i<l;i++)
    {
        if(k&(1<<i))
            ret*=r[i];
        else
            ret*=1-r[i];
    }
    return ret;
}
void brute_force_compute_LR(Fr* L,Fr* R,Fr* r,int l)
{
    for(int k=0;k<(1<<(l/2));k++)
        L[k]=lagrange(r,l/2,k);
    for(int k=0;k<(1<<(l/2));k++)
        R[k]=lagrange(r+l/2,l/2,k);
}
Fr brute_force_compute_eval(Fr* w,Fr* r,int l)
{
    Fr ret=0;
    for(int k=0;k<(1<<l);k++)
        ret+=lagrange(r,l,k)*w[k];
    return ret;
}

G1 compute_Tprime(Fr* w,Fr* r,int l,G1* g,Fr* L) 
{
    //w has 2^l length
    assert(l%2==0);
    int halfl=l/2;
    int rownum=(1<<halfl),colnum=(1<<halfl);
    G1 *Tk=new G1[rownum];
    Fr* row=new Fr[1<<halfl];
    for(int i=0;i<rownum;i++) // enumerate row of T  
    {
        for(int j=0;j<colnum;j++)// enum col
            row[j]=w[i+j*rownum];
        Tk[i]=perdersen_commit(g,row,colnum);
    }
    G1 ret=perdersen_commit(Tk,L,rownum);
    delete []row;
    return ret;
}
G1 compute_LT(Fr*w ,Fr*L,int l,G1*g,Fr*& ret) // L is row number length
{
    int halfl=l/2;
    int rownum=(1<<halfl),colnum=(1<<halfl);
    Fr* res=new Fr[colnum];
    for(int j=0;j<colnum;j++)
    {
        res[j]=0;
        for(int i=0;i<rownum;i++)
            res[j]+=L[i]*w[i+j*rownum];  // mat mult  (1,row)*(row,col)=(1,col)
    }
    G1 comm=perdersen_commit(g,res,colnum);
    ret=res;
    return comm;
}
G1 gen_gi(G1* g,int n)
{
    const char *g1Str = "1 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1";
    G1 base;
    base.setStr(g1Str);
    for(int i=0;i<n;i++)
    {
        Fr tmp;
        tmp.setByCSPRNG();
        g[i]=base*tmp;
    }
    return base;
}
struct Pack 
{
    G1 gamma;
    Fr a;
    G1 g;
    Fr y;
    Fr x;
    Pack(G1 gamm,Fr fa, G1 gg,Fr xx,Fr yy)
    {
        gamma=gamm;
        a=fa;
        g=gg;
        x=xx;
        y=yy;
    }
};
struct Hyrax_proof
{
    //transmitted data
    G1 tprime, comm_w;
    //public data
    G1 *g, G;
    Fr* R;
    //prover only data
    Fr* LT;
    Fr eval;

};
Pack bullet_reduce(G1 gamma, Fr*a,G1*g,int n,G1& G,Fr* x,Fr y,bool need_free=false) // length n
{
    if(n==1)
    {
        Pack p(gamma,a[0],g[0],x[0],y);
        return p;
    }
    timer P(true),V;
    P.start();
    //step2  prover fold
    G1 gamma_minus1,gamma_1;
    Fr x1a2=0,x2a1=0;
    for(int i=0;i<n/2;i++)
    {
        x1a2+=x[i]*a[n/2+i];
        x2a1+=x[n/2+i]*a[i];
    }
    gamma_minus1=G*x1a2+perdersen_commit(g+n/2,x,n/2);
    gamma_1=G*x2a1+perdersen_commit(g,x+n/2,n/2);
    Fr c,invc;
    c.setByCSPRNG();  // step3 V choose random c
    Fr::inv(invc,c);
    P.stop("Bullet proof Part1 fold x dot a",false);
    //prover verifier both comp
    V.start();
    G1 gamma_prime=gamma_minus1*c*c+gamma_1*invc*invc+gamma;
    Fr* aprime=new Fr[n/2];       
    for(int i=0;i<n/2;i++)
        aprime[i]=a[i]*invc+a[i+n/2]*c;
    G1* gprime=new G1[n/2];           
    for(int i=0;i<n/2;i++)
        gprime[i]=g[i]*invc+g[i+n/2]*c;
    V.stop("Verifier ");
    P.stop("Bullet proof Part2 fold a & g",false);
    //prover single compute
    Fr* xprime=new Fr[n/2];         
    Fr yprime;
    for(int i=0;i<n/2;i++)
        xprime[i]=c*x[i]+invc*x[i+n/2];
    yprime=c*c*x1a2+invc*invc*x2a1+y;
    P.stop("Bullet proof Part3 fold x & y",false);
    if(need_free)
    {
        delete []a;
        delete []g;
        delete []x;
    }
    P.stop("Prover Total");
    return bullet_reduce(gamma_prime,aprime,gprime,n/2,G,xprime,yprime,true);
}   

bool prove_dot_product(G1 comm_x, G1 comm_y, Fr* a, G1*g ,G1& G,Fr* x,Fr y,int n)  // y= <a,x> , 
{
    G1 gamma=comm_x+comm_y;
    Pack p=bullet_reduce(gamma,a,g,n,G,x,y);
    assert(p.y==p.x*p.a);
    assert(p.gamma==p.g*p.x+G*p.y);
    return true;
}

Hyrax_proof prover_commit(Fr* w, Fr* r, G1& G,G1* g, Fr*L,Fr*R,int l)
{
    int halfl=l/2;
    int rownum=(1<<halfl),colnum=(1<<halfl);
    Fr* LT;
    timer t(true);
    t.start();
    brute_force_compute_LR(L,R,r,l);
    t.stop("brute force LR ",false);
    G1 tprime=compute_Tprime(w,r,l,g,L);
    t.stop("Tprime ",false);
    Fr eval=brute_force_compute_eval(w,r,l);
    t.stop("eval ",false);
    G1 tprime2=compute_LT(w,L,l,g,LT);
    t.stop("LT ",false);
    assert(tprime==tprime2);
    G1 comm_w=G*eval;
    t.stop("total ",true,false);
    Hyrax_proof h{tprime,comm_w,g,G,R,LT,eval};
    return h;
    //for(int i=0;i<colnum;i++)
    //    wr+=LT[i]*R[i];
    //assert(wr==eval);  // LT dot R = eval
}


const int MAXL=26;
Fr w[(1<<MAXL)],r[MAXL],L[1<<(MAXL/2)],R[1<<(MAXL/2)];
G1 g[1<<(MAXL/2)];

int main(int argc, char *argv[])
{
    initPairing(mcl::BLS12_381);
    int l=24;
    for(int i=0;i<(1<<l);i++)
        w[i]=rand()%65535-30000;

    for(int i=0;i<l;i++)
        r[i].setByCSPRNG();
    G1 G=gen_gi(g,1<<(l/2));
    timer t;
    t.start();
    Hyrax_proof proof=prover_commit(w,r,G,g,L,R,l);
    prove_dot_product(proof.tprime,proof.comm_w,proof.R,proof.g,proof.G,proof.LT,proof.eval,(1<<(l/2)));  // tprime, comm_w ,R,g,G public, LT eval only prover knows
    t.stop("All time: ");
    return 0;
}