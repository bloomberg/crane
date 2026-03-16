// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>

#include "dim10_tower_proof_chain.h"

int main()
{
    assert(Dim10TowerProofChainCase::dim10_p0_dim == 10u);
    assert(Dim10TowerProofChainCase::dim10_p4_dim == 6u);
    assert(Dim10TowerProofChainCase::dim10_p9_dim == 1u);
    assert(Dim10TowerProofChainCase::dim10_p10_dim == 0u);
    assert(Dim10TowerProofChainCase::dim10_p12_dim == 0u);
    assert(Dim10TowerProofChainCase::dim10_d0_dim == 1u);
    assert(Dim10TowerProofChainCase::dim10_d4_dim == 1u);
    assert(Dim10TowerProofChainCase::dim10_d9_dim == 1u);
    assert(Dim10TowerProofChainCase::dim10_d10_dim == 0u);
    assert(Dim10TowerProofChainCase::dim10_layers_cutoff == 10u);
    assert(Dim10TowerProofChainCase::dim10_P_cutoff == 10u);
    assert(Dim10TowerProofChainCase::dim10_layers_cutoff_matches);
    assert(Dim10TowerProofChainCase::dim10_P_cutoff_matches);
    assert(Dim10TowerProofChainCase::dim10_dimension_checksum == 40u);
    return 0;
}
