use sha3::{Digest, Keccak256};
use std::fmt;

use crate::{keys::PublicKey, ristretto::RistrettoPublicKey};
use curve25519_dalek::ristretto::CompressedRistretto;

/// The list of the existing Twilight networks.
/// Network type: Mainnet, Testnet.
/// Network implements [`Default`] and returns [`Network::Mainnet`].
///
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Network {
    /// Mainnet is the "production" network and blockchain.
    Mainnet,
    /// Testnet is the "experimental" network and blockchain where things get released long before
    /// mainnet.
    Testnet,
}
impl Network {
    /// Get the associated magic byte given an address type.
    /// The byte values should be taken from the blockchain config file. The same values should be used here. Sample values are used here
    pub fn as_u8(self, addr_type: &AddressType) -> u8 {
        use AddressType::*;
        match self {
            Network::Mainnet => match addr_type {
                Standard => 12,
                Contract => 24,
            },
            Network::Testnet => match addr_type {
                Standard => 44,
                Contract => 66,
            },
        }
    }

    /// Recover the network type given an address magic byte.
    /// The byte values should be taken from the blockchain config file. The same values should be used here. Sample values are used here
    pub fn from_u8(byte: u8) -> Result<Network, &'static str> {
        use Network::*;
        match byte {
            12 | 24 => Ok(Mainnet),
            44 | 66 => Ok(Testnet),
            _ => Err("Error::InvalidNteworkByte"),
        }
    }
}

impl Default for Network {
    fn default() -> Network {
        Network::Mainnet
    }
}
/// Address type: standard, contract.
///
/// AddressType implements [`Default`] and returns [`AddressType::Standard`].
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum AddressType {
    /// Standard twilight account address.
    Standard,
    /// Contract addresses.
    Contract,
}

impl AddressType {
    /// Recover the address type given an address bytes and the network.
    pub fn from_slice(bytes: &[u8], net: Network) -> Result<AddressType, &'static str> {
        let byte = bytes[0];
        use AddressType::*;
        use Network::*;
        match net {
            Mainnet => match byte {
                12 => Ok(Standard),
                24 => Ok(Contract),
                _ => Err("Error::InvalidAddressTypeMagicByte"),
            },
            Testnet => match byte {
                44 => Ok(Standard),
                66 => Ok(Contract),
                _ => Err("Error::InvalidAddressTypeMagicByte"),
            },
        }
    }
}

impl Default for AddressType {
    fn default() -> AddressType {
        AddressType::Standard
    }
}

impl fmt::Display for AddressType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AddressType::Standard => write!(f, "Standard address"),
            AddressType::Contract => write!(f, "Contract"),
        }
    }
}

/// A complete twilight typed address valid for a specific network.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct Address {
    /// The network on which the address is valid and should be used.
    pub network: Network,
    /// The address type.
    pub addr_type: AddressType,
    /// The address public key.
    pub public_key: RistrettoPublicKey,
}

impl Address {
    /// Create a standard address which is valid on the given network.
    pub fn standard(network: Network, public_key: RistrettoPublicKey) -> Address {
        Address {
            network,
            addr_type: AddressType::Standard,
            public_key,
        }
    }

    /// Create a Contract address which is valid on the given network.
    pub fn contract(network: Network, public_key: RistrettoPublicKey) -> Address {
        Address {
            network,
            addr_type: AddressType::Contract,
            public_key,
        }
    }

    /// Parse an address from a vector of bytes, fail if the magic byte is incorrect, if public
    /// keys are not valid points, and if checksums missmatch.
    pub fn from_bytes(bytes: &[u8]) -> Result<Address, &'static str> {
        let network = Network::from_u8(bytes[0])?;
        let addr_type = AddressType::from_slice(&bytes, network)?;
        let gr = slice_to_pkpoint(&bytes[1..33])?;
        let grsk = slice_to_pkpoint(&bytes[33..65])?;
        let public_key = RistrettoPublicKey { gr, grsk };
        let (checksum_bytes, checksum) = (&bytes[0..65], &bytes[65..69]);
        let mut hasher = Keccak256::new();
        hasher.update(checksum_bytes);
        let checksum_verify = hasher.finalize();
        if &checksum_verify[0..4] != checksum {
            return Err("Invalid Checksum");
        }

        Ok(Address {
            network,
            addr_type,
            public_key,
        })
    }

    /// Serialize the address as a vector of bytes.
    /// Byte Format : [magic byte, public key, checksum]  
    pub fn as_bytes(&self) -> Vec<u8> {
        let mut bytes = vec![self.network.as_u8(&self.addr_type)];
        bytes.extend_from_slice(self.public_key.as_bytes().as_slice());
        let mut hasher = Keccak256::new();
        hasher.update(&bytes);
        let checksum = hasher.finalize();
        bytes.extend_from_slice(&checksum[0..4]);
        bytes
    }

    /// Serialize the address bytes as a hexadecimal string.
    pub fn as_hex(&self) -> String {
        hex::encode(self.as_bytes())
    }

    /// Serialize the address bytes as a BTC-Base58 string.
    pub fn as_base58(&self) -> String {
        bs58::encode(self.as_bytes()).into_string()
    }

    /// Convert Hex address string to Address
    pub fn from_hex(s: &str) -> Self {
        Self::from_bytes(&hex::decode(s).unwrap().as_slice()).unwrap()
    }

    /// Convert Base58 address string to Address
    pub fn from_base58(s: &str) -> Self {
        let decoded = bs58::decode(s).into_vec().unwrap();
        Self::from_bytes(&decoded).unwrap()
    }
}

/// Deserialize a public key from a slice. The input slice is 64 bytes
/// Utility Function
fn slice_to_pkpoint(data: &[u8]) -> Result<CompressedRistretto, &'static str> {
    if data.len() != 32 {
        return Err("Invalid Key Length");
    }
    let gr = CompressedRistretto::from_slice(&data);
    match gr.decompress() {
        Some(_) => (),
        None => {
            return Err("InvalidPoint");
        }
    };
    Ok(gr)
}
// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------
#[cfg(test)]
mod test {
    // use super::*;
    #[test]
    fn hex_encoding_decoding_test() {}
}
