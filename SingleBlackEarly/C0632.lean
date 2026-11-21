import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0632 : checkSingleBlackFast (9, -7) 8155 .west (-7, 0) (-17, -17) = true := by
  decide +kernel

end LangtonsAnt
