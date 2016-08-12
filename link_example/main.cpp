#include <iostream>

#include <common/default_types/ec_pp.hpp>
#include <gadgetlib1/gadgets/basic_gadgets.hpp>
#include <zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>

using namespace libsnark;

typedef default_ec_pp ppT;
typedef Fr<ppT> FieldT;

std::shared_ptr<comparison_gadget<FieldT> > add_smaller_equal(protoboard<FieldT>& pb, const pb_variable<FieldT>& left, const pb_variable<FieldT>& right) {
    pb_variable<FieldT> less, less_or_eq;
    less.allocate(pb);
    less_or_eq.allocate(pb);
    std::shared_ptr<comparison_gadget<FieldT> > ct(new comparison_gadget<FieldT>(pb, 55, left, right, less, less_or_eq));
    ct->generate_r1cs_constraints();
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, less_or_eq, 1));
    return ct;
}

class tx {
    protoboard<FieldT> pb;
    pb_variable_array<FieldT> inputs;
    pb_variable_array<FieldT> outputs;
    pb_variable<FieldT> fee_;
    pb_variable<FieldT> min, max;
    int min_value_, max_value_;
    std::vector<std::shared_ptr<comparison_gadget<FieldT> > > range_constraints;

    void set_primary() {
        pb.val(min) = min_value_;
        pb.val(max) = max_value_;
    }
public:
    r1cs_ppzksnark_keypair<ppT> keypair() {
        return r1cs_ppzksnark_generator<ppT>(pb.get_constraint_system());
    }
    
    tx(int inputs_size, int outputs_size, int min_value, int max_value) {
        default_ec_pp::init_public_params();
        min_value_ = min_value;
        max_value_ = max_value;

        min.allocate(pb);
        max.allocate(pb);

        // make min, max primary inputs
        pb.set_input_sizes(pb.num_variables());
        
        inputs.allocate(pb, inputs_size);
        outputs.allocate(pb, outputs_size);
        fee_.allocate(pb);

        // 1 * (sum(inputs) - sum(outputs) - fee) == 0
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1,
                                                       pb_sum(pb_linear_combination_array<FieldT>(inputs))
                                                       - pb_sum(pb_linear_combination_array<FieldT>(outputs))
                                                       - fee_,
                                                       0));

        for(int i = 0; i < inputs.size(); ++i) {
            range_constraints.push_back(add_smaller_equal(pb, min, inputs[i]));
            range_constraints.push_back(add_smaller_equal(pb, inputs[i], max));
        }
        for(int i = 0; i < outputs.size(); ++i) {
            range_constraints.push_back(add_smaller_equal(pb, min, outputs[i]));
            range_constraints.push_back(add_smaller_equal(pb, outputs[i], max));
        }
        range_constraints.push_back(add_smaller_equal(pb, min, fee_));
        range_constraints.push_back(add_smaller_equal(pb, fee_, max));

    }

    r1cs_ppzksnark_proof<ppT> proof(const r1cs_ppzksnark_proving_key<ppT>& pk,
                                    const std::vector<int>& v_inputs,
                                    const std::vector<int>& v_outputs,
                                    int fee) {
        generate_witness(v_inputs, v_outputs, fee);
        return r1cs_ppzksnark_prover<ppT>(pk,
                                          pb.primary_input(),
                                          pb.auxiliary_input());
    }

    bool verify(const r1cs_ppzksnark_verification_key<ppT>& vk, r1cs_ppzksnark_proof<ppT> proof) {
        set_primary();
        return r1cs_ppzksnark_verifier_strong_IC<ppT>(vk, pb.primary_input(), proof);
    }

private:
    void generate_witness(const std::vector<int>& v_inputs, const std::vector<int>& v_outputs, int fee) {
        set_primary();
        
        for(int i = 0; i < v_inputs.size(); ++i) {
            pb.val(inputs[i]) = v_inputs[i];
        }
        for(int i = 0; i < v_outputs.size(); ++i) {
            pb.val(outputs[i]) = v_outputs[i];
        }
        pb.val(fee_) = fee;

        for(auto iter = range_constraints.begin(); iter != range_constraints.end(); ++iter) {
            (*iter)->generate_r1cs_witness();
        }
        
        assert(pb.is_satisfied());
    }    
};

int main() {
    // Every amount has to be in this range.
    int range_min = 0;
    int range_max = 1000000;

    // Sending some money.
    auto inputs = std::vector<int>();
    inputs.push_back(5);
    inputs.push_back(10);

    // Receiving some money.
    auto outputs = std::vector<int>();
    outputs.push_back(7);
    outputs.push_back(7);

    // Paying a fee.
    int fee = 1;

    tx t(inputs.size(), outputs.size(), range_min, range_max);

    // create proving and verifying key (public, one per circuit board)
    auto kp = t.keypair();

    // Proof that no inflation happened without showing the transaction amounts:
    auto proof = t.proof(kp.pk, inputs, outputs, fee);

    // Verify proof (note: the amounts are not part of the verification!).
    bool ok = tx(inputs.size(), outputs.size(), range_min, range_max).verify(kp.vk, proof);

    assert(ok);
}
