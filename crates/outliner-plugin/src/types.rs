//! Type handles interned for the core, which only ever passes them back.

use std::collections::HashMap;

use binaryninjacore_sys::BNType;
use outliner_core::il::TypeId;

use crate::ffi::TypeRef;

#[derive(Default)]
pub struct TypeTable {
    types: Vec<TypeRef>,
    texts: Vec<Option<String>>,
    by_handle: HashMap<*mut BNType, TypeId>,
}

impl TypeTable {
    pub fn intern(&mut self, t: TypeRef) -> TypeId {
        if let Some(id) = self.by_handle.get(&t.raw()) {
            return *id;
        }
        let id = TypeId(self.types.len() as u32);
        self.by_handle.insert(t.raw(), id);
        self.types.push(t);
        self.texts.push(None);
        id
    }

    pub fn get(&self, id: TypeId) -> &TypeRef {
        &self.types[id.0 as usize]
    }

    /// The type as the core prints it, computed once.
    pub fn text(&mut self, id: TypeId) -> &str {
        let slot = &mut self.texts[id.0 as usize];
        if slot.is_none() {
            *slot = Some(self.types[id.0 as usize].text());
        }
        slot.as_deref().unwrap()
    }
}

/// Type texts compared without whitespace.
pub fn normalize(text: &str) -> String {
    text.split_whitespace().collect()
}
