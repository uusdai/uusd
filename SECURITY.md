# UUSD 安全文档

**创建日期**: 2026-02-03
**最后更新**: 2026-02-03

---

## 1. 合约架构

### 1.1 部署架构

```
┌─────────────────────────────────────────────────────────┐
│                    UUSD Token System                     │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  ┌─────────────────┐      ┌─────────────────┐          │
│  │  Gnosis Safe    │      │   ProxyAdmin    │          │
│  │  (多签钱包)      │      │                 │          │
│  │  Owner          │      │  Owner: Safe    │          │
│  └────────┬────────┘      └────────┬────────┘          │
│           │                        │                    │
│           │ owns                   │ manages upgrades   │
│           ▼                        ▼                    │
│  ┌─────────────────────────────────────────┐           │
│  │     TransparentUpgradeableProxy         │           │
│  │     0x61a10E8556BEd032eA176330e7F17D6a12a10000     │
│  └────────────────────┬────────────────────┘           │
│                       │                                 │
│                       │ delegates to                    │
│                       ▼                                 │
│  ┌─────────────────────────────────────────┐           │
│  │         UUSD Implementation             │           │
│  │     0xA4f44c290CC693fC0c985d679281c61e99d9Be9a     │
│  └─────────────────────────────────────────┘           │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

### 1.2 合约地址 (三链统一)

| 合约 | 地址 | 用途 |
|------|------|------|
| **Proxy (UUSD)** | `0x61a10E8556BEd032eA176330e7F17D6a12a10000` | 用户交互的代币合约 |
| **Implementation** | `0xA4f44c290CC693fC0c985d679281c61e99d9Be9a` | 逻辑实现合约 |
| **ProxyAdmin** | `0x2D49CB4194dFa42d711699a87C10C6BbC05d94b6` | 代理管理合约 |

---

## 2. 权限结构

### 2.1 Gnosis Safe 多签钱包

| 项目 | 值 |
|------|-----|
| **地址** | `0x009c5467667dcD2Ab8C310E84B105cC0b570a8F4` |
| **类型** | Gnosis Safe |
| **签名要求** | [待填写: X/Y 多签] |

**Safe 链接**:
- BNB Chain: https://app.safe.global/home?safe=bnb:0x009c5467667dcD2Ab8C310E84B105cC0b570a8F4
- Ethereum: https://app.safe.global/home?safe=eth:0x009c5467667dcD2Ab8C310E84B105cC0b570a8F4
- Base: https://app.safe.global/home?safe=base:0x009c5467667dcD2Ab8C310E84B105cC0b570a8F4

### 2.2 角色权限矩阵

| 角色 | 权限 | 当前持有者 |
|------|------|-----------|
| **Owner** | mint, burn, setAdmin, addMinter, removeMinter, setMinterAllowance, transferOwnership | Safe 多签 |
| **Admin** | freeze, unfreeze, pause, unpause | 未设置 |
| **Minter** | minterMint (有配额限制), minterBurn | 未设置 |

### 2.3 各链权限状态

| 链 | Owner | ProxyAdmin Owner | Admin | Minter |
|----|-------|------------------|-------|--------|
| BNB Chain | Safe | Safe | 未设置 | 无 |
| Ethereum | Safe | Safe | 未设置 | 无 |
| Base | Safe | Safe | 未设置 | 无 |

---

## 3. 安全配置

### 3.1 已启用的安全机制

| 机制 | 状态 | 说明 |
|------|------|------|
| **Ownable2Step** | ✅ | 两步所有权转移，防止误操作 |
| **renounceOwnership 禁用** | ✅ | 防止合约被锁定 |
| **Pausable** | ✅ | 紧急暂停功能 |
| **Freezable** | ✅ | 账户冻结功能 |
| **Minter 配额限制** | ✅ | 限制 Minter 铸币上限 |
| **多签钱包** | ✅ | Owner 为 Gnosis Safe |

### 3.2 各链合约状态

| 链 | paused | 说明 |
|----|--------|------|
| BNB Chain | `false` | 运行中，准备首发铸币 |
| Ethereum | `true` | 已暂停，等待启用 |
| Base | `true` | 已暂停，等待启用 |

---

## 4. 应急预案

### 4.1 私钥泄露

**情况**: Owner 私钥或 Safe 签名者私钥泄露

**响应步骤**:
1. 立即通过 Safe 执行 `pause()` 暂停合约
2. 检查是否有异常交易
3. 如有必要，`freeze()` 相关地址
4. 更换 Safe 签名者或转移所有权到新 Safe

### 4.2 发现合约漏洞

**情况**: 发现合约逻辑漏洞

**响应步骤**:
1. 立即 `pause()` 暂停合约
2. 评估漏洞影响范围
3. 准备修复版本的 Implementation
4. 通过 ProxyAdmin 执行升级
5. 测试验证后 `unpause()`

### 4.3 黑客攻击

**情况**: 检测到异常大额转账或未授权操作

**响应步骤**:
1. 立即 `pause()` 暂停合约
2. `freeze()` 攻击者地址
3. `freeze()` 已知被盗资金流向地址
4. 分析攻击路径
5. 联系交易所冻结相关资产

---

## 5. 操作审计

### 5.1 部署记录

| 日期 | 链 | 操作 | 交易哈希 |
|------|-----|------|----------|
| 2026-02-03 | BNB Chain | 部署合约 | [查看](https://bscscan.com/address/0x61a10E8556BEd032eA176330e7F17D6a12a10000) |
| 2026-02-03 | Ethereum | 部署合约 | [查看](https://etherscan.io/address/0x61a10E8556BEd032eA176330e7F17D6a12a10000) |
| 2026-02-03 | Base | 部署合约 | [查看](https://basescan.org/address/0x61a10E8556BEd032eA176330e7F17D6a12a10000) |

### 5.2 权限变更记录

| 日期 | 链 | 操作 | 旧值 | 新值 |
|------|-----|------|------|------|
| 2026-02-03 | BNB Chain | Owner 转移 | EOA | Safe |
| 2026-02-03 | BNB Chain | ProxyAdmin Owner 转移 | EOA | Safe |
| 2026-02-03 | Ethereum | Owner 转移 | EOA | Safe |
| 2026-02-03 | Ethereum | ProxyAdmin Owner 转移 | EOA | Safe |
| 2026-02-03 | Ethereum | pause | false | true |
| 2026-02-03 | Base | Owner 转移 | EOA | Safe |
| 2026-02-03 | Base | ProxyAdmin Owner 转移 | EOA | Safe |
| 2026-02-03 | Base | pause | false | true |

### 5.3 铸币/销毁记录

| 日期 | 链 | 操作 | 数量 | 接收地址 | 交易哈希 |
|------|-----|------|------|----------|----------|
| - | - | - | - | - | - |

---

## 6. 监控建议

### 6.1 需监控的事件

| 事件 | 优先级 | 触发条件 |
|------|--------|----------|
| `Transfer` | 高 | 单笔 > 100,000 UUSD |
| `Mint` | 高 | 任何铸币操作 |
| `Burn` | 高 | 任何销毁操作 |
| `Freeze` | 高 | 任何冻结操作 |
| `Pause` | 紧急 | 合约暂停 |
| `OwnershipTransferred` | 紧急 | 所有权变更 |
| `AdminSet` | 高 | Admin 变更 |
| `MinterAdded` | 中 | 添加 Minter |
| `MinterAllowanceSet` | 中 | Minter 配额变更 |

### 6.2 推荐监控工具

- OpenZeppelin Defender
- Tenderly
- Forta
- 自建 Event Listener

---

## 7. 联系方式

### 7.1 紧急联系

| 角色 | 联系方式 |
|------|----------|
| 项目负责人 | [待填写] |
| 技术负责人 | [待填写] |
| 安全负责人 | [待填写] |

### 7.2 外部资源

| 资源 | 链接 |
|------|------|
| 官网 | https://uusd.ai |
| 白皮书 | https://uusd.ai/whitepaper.pdf |
| GitHub | https://github.com/uusdai/uusd |
| Twitter | https://twitter.com/UUSDai |

---

## 8. 版本历史

| 版本 | 日期 | 变更内容 |
|------|------|----------|
| 1.0 | 2026-02-03 | 初始版本，三链部署完成 |
