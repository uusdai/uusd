# UUSD - Unity USD

> **The Native Settlement Layer for AI Economy**

UUSD is a decentralized stablecoin designed as the foundational settlement infrastructure for the emerging AI economy. It enables both humans and AI agents to participate equally in economic activities through a permissionless, peer-to-peer payment system.

## Features

- **ERC-20 Compatible** - Standard token interface with 18 decimals
- **Upgradeable** - Transparent proxy pattern for future improvements
- **Multi-Role Access Control**
  - Owner: Full control, unlimited mint/burn
  - Admin: Freeze/unfreeze accounts, pause/unpause
  - Minter: Mint with allowance limits
- **EIP-2612 Permit** - Gasless approvals via signatures
- **EIP-3009** - Transfer and receive with authorization
- **Batch Transfers** - Up to 200 transfers in one transaction
- **Freeze & Pause** - Security controls for compliance
- **Multi-Chain** - Same address across all EVM chains

## Contract Addresses

Deployed using CREATE2 for deterministic addresses across all EVM-compatible chains:

| Contract | Address |
|----------|---------|
| **UUSD Token (Proxy)** | `0x61a10E8556BEd032eA176330e7F17D6a12a10000` |
| Implementation | `0xA4f44c290CC693fC0c985d679281c61e99d9Be9a` |
| ProxyAdmin | `0x2D49CB4194dFa42d711699a87C10C6BbC05d94b6` |

### Deployed Networks

- [x] BSC Testnet
- [ ] BSC Mainnet
- [ ] Ethereum
- [ ] Base

## Quick Start

### Prerequisites

- [Foundry](https://book.getfoundry.sh/getting-started/installation)
- Node.js >= 18

### Installation

```bash
git clone https://github.com/anthropics/uusd.git
cd uusd
forge install
```

### Build

```bash
forge build
```

### Test

```bash
forge test
```

All 40 tests should pass:

```
[PASS] test_Name()
[PASS] test_Symbol()
[PASS] test_Decimals()
[PASS] test_OwnerMint()
[PASS] test_OwnerBurn()
[PASS] test_TransferWithAuthorization()
... (40 tests total)
```

### Deploy

1. Configure `.env`:

```bash
PRIVATE_KEY=0x...
BSC_RPC_URL=https://bsc-dataseed.binance.org/
BSCSCAN_API_KEY=...
DEPLOY_SALT=0x00000000000000000000000000000000000000000000000000000000000be4b0
```

2. Deploy with CREATE2 (vanity address):

```bash
source .env
forge script script/DeployWithFactory.s.sol:DeployWithFactory \
  --rpc-url $BSC_RPC_URL \
  --broadcast \
  --verify
```

## Documentation

- [Whitepaper (PDF)](docs/whitepaper.pdf)
- [Genesis Document (BitcoinTalk)](https://bitcointalk.org/index.php?topic=5564031.msg65989162)

## Security

### Access Control

| Role | Capabilities |
|------|-------------|
| Owner | Mint/burn unlimited, manage roles, upgrade contract |
| Admin | Freeze/unfreeze accounts, pause/unpause transfers |
| Minter | Mint within allowance, burn own tokens |

### Safety Features

- Two-step ownership transfer (Ownable2Step)
- Frozen accounts cannot send, receive, or spend allowances
- Pause halts all transfers, mints, and burns
- Storage gap reserved for upgrade safety

## Architecture

```
┌─────────────────────────────────────────────────┐
│           TransparentUpgradeableProxy           │
│         0x61a10...a10000 (UUSD Token)           │
├─────────────────────────────────────────────────┤
│                                                 │
│  ┌───────────────┐      ┌──────────────────┐   │
│  │  ProxyAdmin   │      │  Implementation  │   │
│  │  0x2D49CB...  │─────▶│  0xA4f44c...     │   │
│  └───────────────┘      └──────────────────┘   │
│         │                        │              │
│         ▼                        ▼              │
│   Owner Control           UUSD Logic            │
│   (Upgrades)         (ERC20 + Extensions)       │
│                                                 │
└─────────────────────────────────────────────────┘
```

## License

MIT License - see [LICENSE](LICENSE)

## Links

- Website: https://uusd.ai
- Whitepaper: [PDF](docs/whitepaper.pdf) | [BitcoinTalk](https://bitcointalk.org/index.php?topic=5564031.msg65989162)
- Twitter: [@UUSDai](https://twitter.com/UUSDai)
