import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1693 : checkSingleBlackFast2 (-46, -23) 13639 .west (10, 20) (-39, 0) = true := by
  decide +kernel

end LangtonsAnt
