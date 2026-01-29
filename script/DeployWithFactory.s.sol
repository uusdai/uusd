// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Script.sol";
import "@openzeppelin/contracts/proxy/transparent/TransparentUpgradeableProxy.sol";
import "@openzeppelin/contracts/proxy/transparent/ProxyAdmin.sol";
import "../src/UUSD.sol";

/**
 * @title DeployWithFactory
 * @notice Deploy UUSD using Arachnid's CREATE2 Factory for vanity address
 * @dev Factory: 0x4e59b44847b379578588920cA78FbF26c0B4956C (deployed on BSC)
 *
 * Expected addresses with salt 0x...3d60d7:
 * - Proxy (UUSD): 0x61a10E8556BEd032eA176330e7F17D6a12a10000
 * - Implementation: 0xA4f44c290CC693fC0c985d679281c61e99d9Be9a
 * - ProxyAdmin: 0x2D49CB4194dFa42d711699a87C10C6BbC05d94b6
 */
contract DeployWithFactory is Script {
    // Uses CREATE2_FACTORY from forge-std (0x4e59b44847b379578588920cA78FbF26c0B4956C)

    string public constant NAME = "Unity USD";
    string public constant SYMBOL = "UUSD";

    function run() external {
        uint256 deployerPrivateKey = vm.envUint("PRIVATE_KEY");
        bytes32 salt = vm.envBytes32("DEPLOY_SALT");
        address deployer = vm.addr(deployerPrivateKey);

        console.log("=== UUSD Deployment via CREATE2 Factory ===");
        console.log("Deployer:", deployer);
        console.log("Factory:", CREATE2_FACTORY);
        console.log("Salt:");
        console.logBytes32(salt);
        console.log("");

        vm.startBroadcast(deployerPrivateKey);

        // 1. Deploy UUSD Implementation
        bytes memory uusdBytecode = type(UUSD).creationCode;
        address impl = _deployViaFactory(salt, uusdBytecode);
        console.log("Implementation deployed:", impl);

        // 2. Deploy ProxyAdmin
        bytes memory adminBytecode = abi.encodePacked(
            type(ProxyAdmin).creationCode,
            abi.encode(deployer)
        );
        address admin = _deployViaFactory(salt, adminBytecode);
        console.log("ProxyAdmin deployed:", admin);

        // 3. Deploy TransparentUpgradeableProxy
        bytes memory initData = abi.encodeWithSelector(
            UUSD.initialize.selector,
            NAME,
            SYMBOL,
            deployer
        );
        bytes memory proxyBytecode = abi.encodePacked(
            type(TransparentUpgradeableProxy).creationCode,
            abi.encode(impl, admin, initData)
        );
        address proxy = _deployViaFactory(salt, proxyBytecode);
        console.log("Proxy (UUSD) deployed:", proxy);

        vm.stopBroadcast();

        // Verify address ends with a10000
        require(
            uint24(uint160(proxy)) == 0xa10000,
            "Proxy address does not end with a10000!"
        );

        console.log("");
        console.log("=== Deployment Summary ===");
        console.log("UUSD Token:", proxy);
        console.log("Implementation:", impl);
        console.log("ProxyAdmin:", admin);
        console.log("Owner:", deployer);
        console.log("");
        console.log("SUCCESS: Proxy address ends with 'a10000'!");
    }

    function _deployViaFactory(bytes32 salt, bytes memory bytecode) internal returns (address deployed) {
        bytes memory data = abi.encodePacked(salt, bytecode);

        (bool success, bytes memory result) = CREATE2_FACTORY.call(data);
        require(success, "CREATE2 deployment failed");

        // Factory returns the deployed address
        // For Arachnid's factory, the address is returned in the result
        // But we can also compute it
        deployed = _computeCreate2Address(salt, keccak256(bytecode));

        // Verify deployment
        require(deployed.code.length > 0, "Deployment verification failed");
    }

    function _computeCreate2Address(bytes32 salt, bytes32 initCodeHash) internal pure returns (address) {
        return address(uint160(uint256(keccak256(
            abi.encodePacked(bytes1(0xff), CREATE2_FACTORY, salt, initCodeHash)
        ))));
    }
}

/**
 * @title VerifyAddresses
 * @notice Verify computed addresses without deploying
 */
contract VerifyAddresses is Script {
    // Uses CREATE2_FACTORY from forge-std (0x4e59b44847b379578588920cA78FbF26c0B4956C)

    function run() external view {
        bytes32 salt = vm.envBytes32("DEPLOY_SALT");
        address deployer = vm.envAddress("DEPLOYER_ADDRESS");

        console.log("=== Address Verification ===");
        console.log("Salt:");
        console.logBytes32(salt);
        console.log("Deployer:", deployer);
        console.log("");

        // UUSD Implementation
        bytes32 uusdHash = keccak256(type(UUSD).creationCode);
        address impl = _computeCreate2Address(salt, uusdHash);
        console.log("Implementation:", impl);

        // ProxyAdmin
        bytes32 adminHash = keccak256(abi.encodePacked(
            type(ProxyAdmin).creationCode,
            abi.encode(deployer)
        ));
        address admin = _computeCreate2Address(salt, adminHash);
        console.log("ProxyAdmin:", admin);

        // Proxy
        bytes memory initData = abi.encodeWithSelector(
            UUSD.initialize.selector,
            "Unity USD",
            "UUSD",
            deployer
        );
        bytes32 proxyHash = keccak256(abi.encodePacked(
            type(TransparentUpgradeableProxy).creationCode,
            abi.encode(impl, admin, initData)
        ));
        address proxy = _computeCreate2Address(salt, proxyHash);
        console.log("Proxy (UUSD):", proxy);

        console.log("");
        if (uint24(uint160(proxy)) == 0xa10000) {
            console.log("VERIFIED: Proxy ends with 'a10000'!");
        } else {
            console.log("WARNING: Proxy does NOT end with 'a10000'");
        }
    }

    function _computeCreate2Address(bytes32 salt, bytes32 initCodeHash) internal pure returns (address) {
        return address(uint160(uint256(keccak256(
            abi.encodePacked(bytes1(0xff), CREATE2_FACTORY, salt, initCodeHash)
        ))));
    }
}
