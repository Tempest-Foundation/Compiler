let mut PRIVATE_STATE: i32 = 10;

#[export]
pub fn optimized_mutable_owner() i32 {
	PRIVATE_STATE += 1;
	return PRIVATE_STATE;
}