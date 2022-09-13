# 
# ! beacon chain spec -> validator deposit contract (EIP-2982)
# ! 需要搞懂beacon chain处理一个新validator的全过程是什么样的
# * 这里主要就是beacon chain接收信息（BeaconState + Deposit），返回新validator的处理逻辑
def get_validator_from_deposit(state: BeaconState, deposit: Deposit) -> Validator:
    # * amount就是用户传进来的质押金额 -> 最少32ETH（定义成了一个constant）
    amount = deposit.data.amount
    # ! EFFECTIVE_BALANCE_INCREMENT = Gwei(2**0 * 10**9) (= 1,000,000,000, 1 ether)
    # ! MAX_EFFECTIVE_BALANCE = Gwei(2**5 * 10**9) (= 32,000,000,000, 32 ether)

    # * 假如deposit了32ETH -> 一个validator的balance最大是32ETH（这里用了%的方法来取余）
    effective_balance = min(amount - amount % EFFECTIVE_BALANCE_INCREMENT, MAX_EFFECTIVE_BALANCE)

    return Validator(
        # * public key
        pubkey=deposit.data.pubkey,
        # * 提款凭证
        withdrawal_credentials=deposit.data.withdrawal_credentials,
        # * Eligibility -> 应该是被选入validator队列的epoch
        activation_eligibility_epoch=FAR_FUTURE_EPOCH,
        # * 激活成为validator的epoch
        activation_epoch=FAR_FUTURE_EPOCH,
        # ! 退出和提款的epoch，目前都为空 -> merge后（上海分叉）才会开放提款
        exit_epoch=FAR_FUTURE_EPOCH,
        withdrawable_epoch=FAR_FUTURE_EPOCH,
        # * 有效余额 -> 一个validator的最大有效余额是32ETH
        # * 另外还有一个current balance，会加上获取奖励（proposal和attesting）的ether -> 目前最大的有67.9ETH
        effective_balance=effective_balance,
    )

