import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1796 : checkSingleBlackFast2 (-56, -28) 16889 .west (21, 27) (-47, 4) = true := by
  decide +kernel

end LangtonsAnt
