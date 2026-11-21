import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0826 : checkSingleBlackFast2 (21, 1) 19215 .west (-23, -2) (3, -29) = true := by
  decide +kernel

end LangtonsAnt
