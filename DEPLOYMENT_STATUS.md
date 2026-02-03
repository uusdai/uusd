# UUSD 部署状态

**更新时间**: 2026-02-03

## 合约地址 (三链统一)

| 合约 | 地址 |
|------|------|
| **UUSD Token (Proxy)** | `0x61a10E8556BEd032eA176330e7F17D6a12a10000` |
| Implementation | `0xA4f44c290CC693fC0c985d679281c61e99d9Be9a` |
| ProxyAdmin | `0x2D49CB4194dFa42d711699a87C10C6BbC05d94b6` |

## Safe 多签钱包

| 地址 | `0x009c5467667dcD2Ab8C310E84B105cC0b570a8F4` |
|------|---------------------------------------------|

## 各链状态

| 链 | UUSD Owner | ProxyAdmin Owner | Admin | 合约状态 | Total Supply | 浏览器 |
|----|------------|------------------|-------|----------|--------------|--------|
| **BNB Chain** | ✅ Safe | ✅ Safe | 未设置 | 运行中 | 0 | [BscScan](https://bscscan.com/token/0x61a10E8556BEd032eA176330e7F17D6a12a10000) |
| **Ethereum** | ✅ Safe | ✅ Safe | 未设置 | 已暂停 | 0 | [Etherscan](https://etherscan.io/token/0x61a10E8556BEd032eA176330e7F17D6a12a10000) |
| **Base** | ✅ Safe | ✅ Safe | 未设置 | 已暂停 | 0 | [Basescan](https://basescan.org/token/0x61a10E8556BEd032eA176330e7F17D6a12a10000) |

## 合约开源验证

- [x] BNB Chain - 全部验证
- [x] Ethereum - 全部验证
- [x] Base - 全部验证

## 常用操作 (通过 Safe 执行)

### 铸币 (mint)
- **函数**: `mint(uint256 amount)`
- **Data**: `0xa0712d68` + amount (32 bytes)
- **说明**: 铸币到 Safe 地址

### 铸币到指定地址 (mintTo)
- **函数**: `mintTo(address to, uint256 amount)`
- **Data**: `0x449a52f8` + to (32 bytes) + amount (32 bytes)

### 销毁 (burn)
- **函数**: `burn(uint256 amount)`
- **Data**: `0x42966c68` + amount (32 bytes)

### 设置 Admin
- **函数**: `setAdmin(address newAdmin)`
- **Data**: `0x704b6c02` + newAdmin (32 bytes)

### 添加 Minter
- **函数**: `addMinter(address minter)`
- **Data**: `0x983b2d56` + minter (32 bytes)

### 设置 Minter 配额
- **函数**: `setMinterAllowance(address minter, uint256 amount)`
- **Data**: `0x87f7f9b5` + minter (32 bytes) + amount (32 bytes)

### 冻结账户
- **函数**: `freeze(address account)`
- **Data**: `0x8d1fdf2f` + account (32 bytes)

### 解冻账户
- **函数**: `unfreeze(address account)`
- **Data**: `0x45c8b1a6` + account (32 bytes)

### 暂停合约
- **函数**: `pause()`
- **Data**: `0x8456cb59`

### 恢复合约
- **函数**: `unpause()`
- **Data**: `0x3f4ba83a`

## RPC 端点

| 链 | RPC URL |
|----|---------|
| BNB Chain | `https://bsc-dataseed.binance.org/` |
| Ethereum | `https://ethereum-rpc.publicnode.com` |
| Base | `https://mainnet.base.org` |

## Safe 链接

| 链 | Safe URL |
|----|----------|
| BNB Chain | https://app.safe.global/home?safe=bnb:0x009c5467667dcD2Ab8C310E84B105cC0b570a8F4 |
| Ethereum | https://app.safe.global/home?safe=eth:0x009c5467667dcD2Ab8C310E84B105cC0b570a8F4 |
| Base | https://app.safe.global/home?safe=base:0x009c5467667dcD2Ab8C310E84B105cC0b570a8F4 |

## 待办事项

- [ ] BNB Chain 首发铸币
- [ ] 设置 Admin 地址 (可选)
- [ ] 设置 Minter 及配额 (可选)
