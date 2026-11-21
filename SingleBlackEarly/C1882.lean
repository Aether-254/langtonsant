import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1882 : checkSingleBlackFast2 (-63, -37) 12620 .north (20, 12) (-46, -28) = true := by
  decide +kernel

end LangtonsAnt
