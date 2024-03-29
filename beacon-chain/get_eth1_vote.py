def compute_time_at_slot(state: BeaconState, slot: Slot) -> uint64:
    return uint64(state.genesis_time + slot * SECONDS_PER_SLOT)

def voting_period_start_time(state: BeaconState) -> uint64:
    eth1_voting_period_start_slot = Slot(state.slot - state.slot % (EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH))
    return compute_time_at_slot(state, eth1_voting_period_start_slot)

def is_candidate_block(block: Eth1Block, period_start: uint64) -> bool:
    return (
        block.timestamp + SECONDS_PER_ETH1_BLOCK * ETH1_FOLLOW_DISTANCE <= period_start
        and block.timestamp + SECONDS_PER_ETH1_BLOCK * ETH1_FOLLOW_DISTANCE * 2 >= period_start
    )

def get_eth1_vote(state: BeaconState, eth1_chain: Sequence[Eth1Block]) -> Eth1Data:
    period_start = voting_period_start_time(state)
    # * eth1 chain貌似表示主链中的所有blocks，按区块高度，升序排序 -> 最上面的是最新的
    # `eth1_chain` abstractly represents all blocks in the eth1 chain sorted by ascending block height
    votes_to_consider = [
        # * 从eth1 chain中取出对应的block
        get_eth1_data(block) for block in eth1_chain
        if (
            # * 找到candidate block（这是什么东西）
            # ! 我觉得这里应该是递归，从上往下，找到最近的一个标准block（有可能是被finalized的block）
            is_candidate_block(block, period_start)
            # Ensure cannot move back to earlier deposit contract states
            # * get_eth1_data函数，输入一个eth1 block，返回对应的eth1 data
            # * 说明deposit count顺序正确，递增
            and get_eth1_data(block).deposit_count >= state.eth1_data.deposit_count
        )
    ]

    # Valid votes already cast during this period
    # * 有效投票数
    valid_votes = [vote for vote in state.eth1_data_votes if vote in votes_to_consider]

    # Default vote on latest eth1 block data in the period range unless eth1 chain is not live
    # Non-substantive casting for linter
    state_eth1_data: Eth1Data = state.eth1_data
    default_vote = votes_to_consider[len(votes_to_consider) - 1] if any(votes_to_consider) else state_eth1_data

    return max(
        valid_votes,
        key=lambda v: (valid_votes.count(v), -valid_votes.index(v)),  # Tiebreak by smallest distance
        default=default_vote
    )