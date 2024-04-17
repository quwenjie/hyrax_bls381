//
// Created by juzix on 2021/6/17.
//
#define NDEBUG
#include "typedef.hpp"
#include "polyProver.hpp"
#include "polyVerifier.hpp"
#include <bits/stdc++.h>
#include <mcl/bls12_381.hpp>
#include <iostream>
using namespace std;
using std::vector;
using std::string;
using namespace hyrax_bls12_381;
using namespace mcl::bn;

#define LOGN_ID 0
#define PT_ID 1
#define VT_ID 2
#define PS_ID 3

vector<string> ans(4);

template <typename T>
string to_string_wp(const T a_value, const int n = 4) {
    std::ostringstream out;
    out.precision(n);
    out << std::fixed << a_value;
    return out.str();
}

int main(int argc, char *argv[]) {
    u8 logn = argc == 1 ? 10 : atoi(argv[1]);

    initPairing(mcl::BLS12_381);
    u64 n = 1ULL << logn;
    u64 n_sqrt = 1ULL << (logn - (logn >> 1));
    vector<Fr> poly_coeff(n);
    vector<G1> gens(n_sqrt);
    vector<Fr> r(logn);
    const char *g1Str = "1 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1";
    G1 base;
    base.setStr(g1Str);
    for (u64 i = 0; i < n; ++i) poly_coeff[i].setByCSPRNG();
    for (u64 i = 0; i < n_sqrt; ++i) {
        Fr tmp;
        tmp.setByCSPRNG();
        
        
        gens[i] = base * tmp;
    }
    for (u8 i = 0; i < logn; ++i) r[i].setByCSPRNG();
    hyrax_bls12_381::polyProver p(poly_coeff, gens);
    hyrax_bls12_381::polyVerifier v(p, gens);
    Fr RZL=p.evaluate(r);
    bool ret =v.verify(r,RZL );
    assert(ret);
    cout<<ret<<endl;
    ans[LOGN_ID] = std::to_string(logn);
    ans[PT_ID] = to_string_wp(p.getPT());
    ans[VT_ID] = to_string_wp(v.getVT());
    ans[PS_ID] = to_string_wp(p.getPS());

    for (int i = 0; i < ans.size(); ++i)
        printf("%s, ", ans[i].c_str());
    puts("");
    return 0;
}
