import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0654 : checkSingleBlackFast (10, -10) 5073 .west (-7, 3) (-17, -8) = true := by
  decide +kernel

end LangtonsAnt
