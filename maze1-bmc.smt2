(set-option :produce-models true)
(set-logic ALL)
(declare-fun |error_0| () Int)
(declare-fun |this_0| () Int)
;; (declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
;; (declare-datatypes ((|tx_type| 0)) (((|tx_type| (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.prevrandao| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| |bytes_tuple|) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))
;; (declare-fun |tx_0| () |tx_type|)
;; (declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
;; (declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))
;; (declare-fun |crypto_0| () |crypto_type|)
;; (declare-datatypes ((|abi_type| 0)) (((|abi_type|))))
;; (declare-fun |abi_0| () |abi_type|)
;; (declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))
;; (declare-fun |state_0| () |state_type|)
(declare-fun |x_8_0| () Int)
(declare-fun |y_10_0| () Int)
(declare-fun |p0_12_0| () Int)
(declare-fun |p1_14_0| () Int)
(declare-fun |p2_16_0| () Int)
(declare-fun |p3_18_0| () Int)
(declare-fun |p4_20_0| () Int)
(declare-fun |p5_22_0| () Int)
(declare-fun |p6_24_0| () Int)
(declare-fun |p7_26_0| () Int)
(declare-fun |_29_0| () Int)
(declare-fun |ny_32_0| () Int)
(declare-fun |x_8_1| () Int)
(declare-fun |y_10_1| () Int)
(declare-fun |expr_33_0| () Int)
(declare-fun |expr_34_0| () Int)
(declare-fun |expr_35_1| () Int)
(declare-fun |ny_32_1| () Int)
(declare-fun |expr_38_0| () Int)
(declare-fun |expr_39_0| () Int)
(declare-fun |expr_40_1| () Bool)

(assert (and (and true true) (and (= expr_40_1 (< expr_38_0 expr_39_0)) (and (=> (and true true) true) (and (= expr_39_0 7) (and (=> (and true true) (and (>= expr_38_0 0) (<= expr_38_0 18446744073709551615))) (and (= expr_38_0 ny_32_1) (and (ite (and true true) (= ny_32_1 expr_35_1) (= ny_32_1 ny_32_0)) (and (=> (and true true) (and (>= expr_35_1 0) (<= expr_35_1 18446744073709551615))) (and (= expr_35_1 (+ expr_33_0 expr_34_0)) (and (=> (and true true) true) (and (= expr_34_0 1) (and (=> (and true true) (and (>= expr_33_0 0) (<= expr_33_0 18446744073709551615))) (and (= expr_33_0 y_10_1) (and (= _29_0 0) (and (and (>= p7_26_0 0) (<= p7_26_0 18446744073709551615)) (and (and (>= p6_24_0 0) (<= p6_24_0 18446744073709551615)) (and (and (>= p5_22_0 0) (<= p5_22_0 18446744073709551615)) (and (and (>= p4_20_0 0) (<= p4_20_0 18446744073709551615)) (and (and (>= p3_18_0 0) (<= p3_18_0 18446744073709551615)) (and (and (>= p2_16_0 0) (<= p2_16_0 18446744073709551615)) (and (and (>= p1_14_0 0) (<= p1_14_0 18446744073709551615)) (and (and (>= p0_12_0 0) (<= p0_12_0 18446744073709551615)) (and (= ny_32_0 0) (and (and (>= y_10_1 0) (<= y_10_1 18446744073709551615)) (and (and (>= x_8_1 0) (<= x_8_1 18446744073709551615)))))))))))))))))))))))))) (not expr_40_1)))
(check-sat)