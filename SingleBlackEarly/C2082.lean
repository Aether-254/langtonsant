import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2082 : checkSingleBlackFast2 (-82, -54) 18241 .west (34, 40) (-60, 17) = true := by
  decide +kernel

end LangtonsAnt
