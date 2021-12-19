# pvss_based_on_cpabe

## setup 

CP-ABE setup algorithm (by the dealer)

## keygenAndElgamalEncAndVerify 

generate PVSS shares using CP-ABE keygen algorithm (by the dealer)

Encrypt the shares using ElGamal encryption, associated with the corresponding NIZK proofs (by the dealer)

Verify the encrypted shares using the NIZK proofs (by arbitary external verifier)

## encryptAndVerify 

generate the commitment using CP-ABE encrypt algorithm, associated with the corresponding NIZK proofs (by the dealer)

Verify the commitment using the NIZK proofs (by arbitary external verifier)


## decrypt

reconstruct the secret using CP-ABE decrypt algorithm (by arbitary external verifier, who gains t honest decrypted shares after verifying them)