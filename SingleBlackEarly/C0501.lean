import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0501 : checkSingleBlackFast (-1, 15) 4064 .south (-9, -10) (-17, -10) = true := by
  decide +kernel

end LangtonsAnt
