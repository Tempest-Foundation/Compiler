import "optimized_owner.sl";

#[export]
pub fn optimized_caller() i32 {
	return optimized_owner();
}