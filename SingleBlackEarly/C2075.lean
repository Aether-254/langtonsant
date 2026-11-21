import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2075 : checkSingleBlackFast (-78, -59) 21856 .north (41, 37) (-67, -29) = true := by
  decide +kernel

end LangtonsAnt
