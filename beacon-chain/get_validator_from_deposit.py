# 
# ! beacon chain spec -> validator deposit contract (EIP-2982)
# * 这里主要就是beacon chain接收信息（BeaconState + Deposit），返回新validator的处理逻辑
def get_validator_from_deposit(state: BeaconState, deposit: Deposit) -> Validator:
    # * amount就是用户传进来的质押金额 -> 最少32ETH（定义成了一个constant）
    amount = deposit.data.amount
    # ! EFFECTIVE_BALANCE_INCREMENT = Gwei(2**0 * 10**9) (= 1,000,000,000)
    # ! MAX_EFFECTIVE_BALANCE = Gwei(2**5 * 10**9) (= 32,000,000,000)
    effective_balance = min(amount - amount % EFFECTIVE_BALANCE_INCREMENT, MAX_EFFECTIVE_BALANCE)

    return Validator(
        pubkey=deposit.data.pubkey,
        withdrawal_credentials=deposit.data.withdrawal_credentials,
        activation_eligibility_epoch=FAR_FUTURE_EPOCH,
        activation_epoch=FAR_FUTURE_EPOCH,
        exit_epoch=FAR_FUTURE_EPOCH,
        withdrawable_epoch=FAR_FUTURE_EPOCH,
        effective_balance=effective_balance,
    )

