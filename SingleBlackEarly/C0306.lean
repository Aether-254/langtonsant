import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0306 : checkSingleBlackFast (5, 13) 3227 .west (-3, 2) (-17, -7) = true := by
  decide +kernel

end LangtonsAnt
