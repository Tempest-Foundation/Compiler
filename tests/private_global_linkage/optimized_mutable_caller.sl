import "optimized_mutable_owner.sl";

#[export]
pub fn optimized_mutable_caller() i32 {
	return optimized_mutable_owner();
}