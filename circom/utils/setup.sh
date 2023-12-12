snarkjs powersoftau new bn128 17 pot17_0000.ptau -v
snarkjs powersoftau contribute pot17_0000.ptau pot17_0001.ptau --name="First contribution" -v
snarkjs powersoftau prepare phase2 pot17_0001.ptau pot17_final.ptau -v
snarkjs groth16 setup runner.r1cs pot17_final.ptau runner_0000.zkey
snarkjs zkey contribute runner_0000.zkey runner_0001.zkey --name="1st Contributor Name" -v
snarkjs zkey export verificationkey runner_0001.zkey verification_key.json
