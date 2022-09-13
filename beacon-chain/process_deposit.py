# 
# ! beacon chain处理validator质押32ETH的具体逻辑 -> 非常的细节
def process_deposit(state: BeaconState, deposit: Deposit) -> None:
    # Verify the Merkle branch
    # * 验证数据的正确性
    assert is_valid_merkle_branch(
        leaf=hash_tree_root(deposit.data),
        branch=deposit.proof,
        depth=DEPOSIT_CONTRACT_TREE_DEPTH + 1,  # Add 1 for the List length mix-in
        index=state.eth1_deposit_index,
        root=state.eth1_data.deposit_root,
    )

    # Deposits must be processed in order
    # * 新的质押交易 -> deposit_index加1
    # * eth1_deposit_index是BeaconState中的一个参数
    state.eth1_deposit_index += 1

    pubkey = deposit.data.pubkey
    amount = deposit.data.amount
    # * 拿出validator list里面的所有pubkey
    validator_pubkeys = [v.pubkey for v in state.validators]
    # * 如果pubkey不在pubkey list里面
    if pubkey not in validator_pubkeys:
        # Verify the deposit signature (proof of possession) which is not checked by the deposit contract
        # * 验证deposit signature
        deposit_message = DepositMessage(
            pubkey=deposit.data.pubkey,
            withdrawal_credentials=deposit.data.withdrawal_credentials,
            amount=deposit.data.amount,
        )
        domain = compute_domain(DOMAIN_DEPOSIT)  # Fork-agnostic domain since deposits are valid across forks
        signing_root = compute_signing_root(deposit_message, domain)
        if not bls.Verify(pubkey, signing_root, deposit.data.signature):
            return

        # Add validator and balance entries
        # * 验证签名正确，把信息添加到state中（新的validator）
        # * 调用get_v_from_deposit函数，传入state和deposit，拿到新的validator对象，并存储到state validator list当中
        state.validators.append(get_validator_from_deposit(state, deposit))
        # * 添加对应（新注册validator）的balance
        state.balances.append(amount)
    else:
        # Increase balance by deposit amount
        index = ValidatorIndex(validator_pubkeys.index(pubkey))
        # * 如果有pubkey（说明不是新增的validator），直接把这个validator的数据添加进去即可
        increase_balance(state, index, amount)