import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0382 : checkSingleBlackFast (14, 2) 4842 .south (-12, -2) (-17, -7) = true := by
  decide +kernel

end LangtonsAnt
