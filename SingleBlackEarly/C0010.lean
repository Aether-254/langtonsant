import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0010 : checkSingleBlackFast (-2, -2) 4184 .south (-5, -4) (-17, -10) = true := by
  decide +kernel

end LangtonsAnt
