//
// Created by juzix on 2021/6/17.
//
#undef NDEBUG
#include <mcl/bls12_381.hpp>
#include <iostream>
#include "hyrax.hpp"
using namespace std;

using namespace mcl::bn;
using namespace hyrax;

const int MAXL=29;
ll ww[(1<<MAXL)];
Fr w[(1<<MAXL)];
Fr r[MAXL],L[1<<(MAXL/2+1)],R[1<<(MAXL/2+1)];
G1 g[1<<(MAXL/2+1)];
void field(const char* f,Fr x)
{
    if(x.isNegative())
        cout<<f<<" -"<<-x<<endl;
    else
        cout<<f<<" "<<x<<endl;
    
}
int main(int argc, char *argv[])
{
    initPairing(mcl::BLS12_381);
    int l=28;
    for(int i=0;i<(1<<l)-100;i++)
    {
        ww[i]=1ll*(rand()%2000-1000);
        w[i]=ww[i];
    }
    for(int i=(1<<l)-50;i<(1<<l);i++)
    {
        if(i&1)
            ww[i]=1ll<<63;
        else    
            ww[i]=(1ll<<63)-i;
        w[i]=ww[i];
    }
   
    for(int i=0;i<l;i++)
        r[i].setByCSPRNG();
    int rownum=1<<(l/2);
    int colnum=1<<(l-l/2);
    G1 G=gen_gi(g,colnum);
    timer t;
    t.start();
    G1*tk=prover_commit(ww,g,l,16);  //77s, ppg: 
    //t.stop("commit time: ");
    Fr eva=prover_evaluate(w,r,G,g,L,R,l);
    hyrax::verify(w,r,eva,G,g,L,R,tk,l);  // tprime, comm_w ,R,g,G public, LT eval only prover knows
    t.stop("All time: ");
    return 0;
}


//TODO: long long 1x slower than int, should optimize