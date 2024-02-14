from ape import accounts, networks, project

def main():
    network = networks.provider.network.name
    chain_id = networks.provider.network.chain_id
    assert chain_id == 17000, f'only for deploy on holesky, not {network}({chain_id})'
    deployer = accounts[0]
    max_fee = '1 gwei'
    max_priority_fee = '0.01 gwei'
    print(f'deployer: {deployer.address}')
    weth_address = '0x94373a4919B3240D86eA41593D5eBa789FEF3848'
    vrun = project.main.deploy(weth_address, sender=deployer, max_fee=max_fee, max_priority_fee=max_priority_fee)
