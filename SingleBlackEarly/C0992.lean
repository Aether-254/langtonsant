import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0992 : checkSingleBlackFast (-4, 16) 8011 .east (-2, -3) (-18, -18) = true := by
  decide +kernel

end LangtonsAnt
