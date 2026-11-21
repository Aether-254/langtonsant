import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0505 : checkSingleBlackFast (-6, 2) 6893 .west (-7, 3) (-17, -18) = true := by
  decide +kernel

end LangtonsAnt
