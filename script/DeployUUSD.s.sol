// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Script.sol";
import "@openzeppelin/contracts/proxy/transparent/TransparentUpgradeableProxy.sol";
import "@openzeppelin/contracts/proxy/transparent/ProxyAdmin.sol";
import "../src/UUSD.sol";

/**
 * @title DeployUUSD
 * @notice Deployment script for UUSD token with TransparentUpgradeableProxy
 */
contract DeployUUSD is Script {
    string public constant NAME = "Unity USD";
    string public constant SYMBOL = "UUSD";

    function run() external {
        uint256 deployerPrivateKey = vm.envUint("PRIVATE_KEY");
        address deployer = vm.addr(deployerPrivateKey);

        console.log("Deploying UUSD...");
        console.log("Deployer:", deployer);

        vm.startBroadcast(deployerPrivateKey);

        // 1. Deploy implementation
        UUSD implementation = new UUSD();
        console.log("Implementation deployed at:", address(implementation));

        // 2. Deploy ProxyAdmin
        ProxyAdmin proxyAdmin = new ProxyAdmin(deployer);
        console.log("ProxyAdmin deployed at:", address(proxyAdmin));

        // 3. Encode initialize call
        bytes memory initData = abi.encodeWithSelector(
            UUSD.initialize.selector,
            NAME,
            SYMBOL,
            deployer
        );

        // 4. Deploy TransparentUpgradeableProxy
        TransparentUpgradeableProxy proxy = new TransparentUpgradeableProxy(
            address(implementation),
            address(proxyAdmin),
            initData
        );
        console.log("Proxy (UUSD) deployed at:", address(proxy));

        // 5. Initialize implementation directly to prevent uninitialized impl
        // Note: This will revert if already initialized, which is fine
        try implementation.initialize("", "", address(0)) {
            // Should not reach here in normal cases
        } catch {
            // Expected: implementation already initialized by constructor disabling
        }

        vm.stopBroadcast();

        console.log("");
        console.log("=== Deployment Summary ===");
        console.log("UUSD Token (Proxy):", address(proxy));
        console.log("Implementation:", address(implementation));
        console.log("ProxyAdmin:", address(proxyAdmin));
        console.log("Owner:", deployer);
    }
}

/**
 * @title DeployUUSDWithSalt
 * @notice Deployment script using CREATE2 for vanity address
 * @dev Use external tools (create2crunch, etc.) to find the salt first
 *
 * Usage:
 * 1. Find salt using vanity mining tool
 * 2. Set DEPLOY_SALT env var
 * 3. Run: forge script script/DeployUUSD.s.sol:DeployUUSDWithSalt --rpc-url $BSC_RPC_URL --broadcast
 */
contract DeployUUSDWithSalt is Script {
    string public constant NAME = "Unity USD";
    string public constant SYMBOL = "UUSD";

    function run() external {
        uint256 deployerPrivateKey = vm.envUint("PRIVATE_KEY");
        address deployer = vm.addr(deployerPrivateKey);
        bytes32 salt = vm.envBytes32("DEPLOY_SALT");

        console.log("Deploying UUSD with CREATE2...");
        console.log("Deployer:", deployer);
        console.log("Salt:", vm.toString(salt));

        vm.startBroadcast(deployerPrivateKey);

        // 1. Deploy implementation with CREATE2
        UUSD implementation = new UUSD{salt: salt}();
        console.log("Implementation deployed at:", address(implementation));

        // 2. Deploy ProxyAdmin with CREATE2
        ProxyAdmin proxyAdmin = new ProxyAdmin{salt: salt}(deployer);
        console.log("ProxyAdmin deployed at:", address(proxyAdmin));

        // 3. Encode initialize call
        bytes memory initData = abi.encodeWithSelector(
            UUSD.initialize.selector,
            NAME,
            SYMBOL,
            deployer
        );

        // 4. Deploy TransparentUpgradeableProxy with CREATE2
        TransparentUpgradeableProxy proxy = new TransparentUpgradeableProxy{salt: salt}(
            address(implementation),
            address(proxyAdmin),
            initData
        );
        console.log("Proxy (UUSD) deployed at:", address(proxy));

        vm.stopBroadcast();

        console.log("");
        console.log("=== Deployment Summary ===");
        console.log("UUSD Token (Proxy):", address(proxy));
        console.log("Implementation:", address(implementation));
        console.log("ProxyAdmin:", address(proxyAdmin));
        console.log("Owner:", deployer);
    }

    /**
     * @notice Helper to compute CREATE2 address for proxy
     * @param deployer Deployer address
     * @param salt Salt value
     */
    function computeProxyAddress(address deployer, bytes32 salt) external view returns (address) {
        // Implementation bytecode hash
        bytes32 implCreationCodeHash = keccak256(type(UUSD).creationCode);
        address impl = computeCreate2Address(deployer, salt, implCreationCodeHash);

        // ProxyAdmin bytecode hash
        bytes32 adminCreationCodeHash = keccak256(
            abi.encodePacked(type(ProxyAdmin).creationCode, abi.encode(deployer))
        );
        address admin = computeCreate2Address(deployer, salt, adminCreationCodeHash);

        // Proxy bytecode hash
        bytes memory initData = abi.encodeWithSelector(
            UUSD.initialize.selector,
            NAME,
            SYMBOL,
            deployer
        );
        bytes32 proxyCreationCodeHash = keccak256(
            abi.encodePacked(
                type(TransparentUpgradeableProxy).creationCode,
                abi.encode(impl, admin, initData)
            )
        );

        return computeCreate2Address(deployer, salt, proxyCreationCodeHash);
    }

    function computeCreate2Address(
        address deployer,
        bytes32 salt,
        bytes32 creationCodeHash
    ) internal pure returns (address) {
        return address(
            uint160(
                uint256(
                    keccak256(
                        abi.encodePacked(bytes1(0xff), deployer, salt, creationCodeHash)
                    )
                )
            )
        );
    }
}
