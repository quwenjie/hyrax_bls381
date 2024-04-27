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

const int MAXL=26;

ll ww[(1<<MAXL)];
Fr w[(1<<MAXL)];
Fr r[MAXL],L[1<<(MAXL/2)],R[1<<(MAXL/2)];
G1 g[1<<(MAXL/2)];

int main(int argc, char *argv[])
{
    initPairing(mcl::BLS12_381);
    int l=23;
    for(int i=0;i<(1<<l)-100;i++)
    {
        ww[i]=1ll*(rand()%2000-1000);
        w[i]=ww[i];
    }
    for(int i=(1<<l)-50000;i<(1<<l);i++)
    {
        ww[i]=1ll*(rand()%600-300)*rand()*rand()*rand();
        w[i]=ww[i];
    }
    
    for(int i=0;i<l;i++)
        r[i].setByCSPRNG();
    G1 G=gen_gi(g,1<<(l/2));
    timer t;
    t.start();
    G1*tk=prover_commit(ww,g,l,16);  //77s, ppg: 
    cerr<<"end here"<<endl;
    //w[0]+=1;
    Fr eva=prover_evaluate(w,r,G,g,L,R,l);
    hyrax::verify(w,r,eva,G,g,L,R,tk,l);  // tprime, comm_w ,R,g,G public, LT eval only prover knows
    t.stop("All time: ");
    return 0;
}


//TODO: long long 1x slower than int, should optimize