sed -i -e 's/pub struct rosidl_message_type_support_t/struct rosidl_message_type_support_t_/' $1
sed -i -e 's/pub struct rosidl_service_type_support_t/struct rosidl_service_type_support_t_/' $1
sed -i '1ipub use safe_drive::rcl::{rosidl_message_type_support_t, rosidl_service_type_support_t};' $1
